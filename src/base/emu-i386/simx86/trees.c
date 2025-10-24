/***************************************************************************
 *
 * All modifications in this file to the original code are
 * (C) Copyright 1992, ..., 2014 the "DOSEMU-Development-Team".
 *
 * for details see file COPYING in the DOSEMU distribution
 *
 *
 *  SIMX86 a Intel 80x86 cpu emulator
 *  Copyright (C) 1997,2001 Alberto Vignani, FIAT Research Center
 *				a.vignani@crf.it
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Additional copyright notes:
 *
 * 1. The kernel-level vm86 handling was taken out of the Linux kernel
 *  (linux/arch/i386/kernel/vm86.c). This code originally was written by
 *  Linus Torvalds with later enhancements by Lutz Molgedey and Hans Lermen.
 *
 * 2. The tree handling routines were adapted from libavl:
 *  libavl - manipulates AVL trees.
 *  Copyright (C) 1998, 1999 Free Software Foundation, Inc.
 *  The author may be contacted at <pfaffben@pilot.msu.edu> on the
 *  Internet, or as Ben Pfaff, 12167 Airport Rd, DeWitt MI 48820, USA
 *  through more mundane means.
 *
 ***************************************************************************/

#include <stddef.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/mman.h>
#include "emu86.h"
#include "misc/dlmalloc.h"
#include "codegen.h"

IMeta	InstrMeta[MAXINODES];
int	CurrIMeta = -1;
TNode *BrokenNode;

/* Tree structure to store collected code sequences */
static IntervalTreeRoot ITreeRoot;
static IntervalTreeNode *Traverser = NULL;
static int ninodes = 0;
static pthread_mutex_t trees_mtx = PTHREAD_MUTEX_INITIALIZER;

int NodesParsed = 0;
int NodesExecd = 0;
int NodesPrejitted = 0;
int CleanFreq = 8;
int CreationIndex = 0;

#if PROFILE
int MaxDepth = 0;
int MaxNodes = 0;
int MaxNodeSize = 0;
int TotalNodesParsed = 0;
int TotalNodesExecd = 0;
int PrejitNodesExecd = 0;
int NodesFound = 0;
int NodesFastFound = 0;
int NodesNotFound = 0;
int TreeCleanups = 0;
#endif

#ifdef DEBUG_TREE
static void DumpTree (FILE *fd);
#endif

#define FINDTREE_CACHE_HASH_MASK 0xfff
static TNode *findtree_cache[FINDTREE_CACHE_HASH_MASK+1];

static int NodeLimit = 10000;

#define RANGE_INTERSECT(al,ah,l,h)	({int _l2=(al);\
	int _h2=(ah); ((_h2 > (l)) && (_l2 < (h))); })
#define ADDR_IN_RANGE(a,l,h)		({typeof(a) _a2=(a);	\
	((_a2 >= (l)) && (_a2 < (h))); })

/////////////////////////////////////////////////////////////////////////////

/*
 * Given addr with translated code (from e.g., a fault) find the
 * corresponding original PC. This is slow but it's only used for
 * DPMI exceptions.
 */
unsigned int FindPC(const unsigned char *addr)
{
  IntervalTreeNode *p = interval_tree_iter_first(&ITreeRoot, 0, 0xffffffffu);
  TNode *G;
  unsigned char *ahE;
  Addr2Pc *AP;
  unsigned int i;

  for (;;) {
      /* walk to next node */
      G = container_of(p, TNode, itree);
      ahE = G->addr + G->len;
      if (!ADDR_IN_RANGE(addr,G->addr,ahE)) {
	p = interval_tree_iter_next(p, 0, 0xffffffffu);
	if (!p) break;
	continue;
      }
      e_printf("### FindPC: Found node %p->%p..%p", addr,G->addr,ahE);
      AP = G->pmeta;
      for (i=0; i<G->seqnum; i++) {
	  e_printf("     %08x:%p",(G->itree.start+AP->dnpc),G->addr+AP->daddr);
	  if (addr < G->addr+AP->daddr) break;
	  AP++;
      }
      e_printf("\nFindPC: PC=%x\n", G->itree.start+(AP-1)->dnpc);
      return G->itree.start+(AP-1)->dnpc;
  }
  return 0;
}

/////////////////////////////////////////////////////////////////////////////
/*
 * The node linker.
 *
 * For the x86 target, code sequence can have one of three termination types:
 *
 *	1) straight end (no jump), or unconditional jump or call
 *
 *	key:	|
 *		|
 *		|
 *		mov $next_addr,eax
 *		pop edx (flags)
 *		ret
 *
 *	2) conditional jump or loop
 *
 *	key:	|
 *		|
 *		|
 *		jcond taken
 *		<optional signal check code (CKSIGN)>
 *		mov $not_taken_addr,eax
 *		pop edx (flags)
 *		ret
 *	taken:  <optional signal check code (JB_LINK)>
 *		mov $taken_addr,eax
 *		pop edx (flags)
 *		ret
 *
 *      3) indirect jump or ret
 *	key:	|
 *		| <eax is new IP>
 *		add eax, <CS Base>
 *		pop edx (flags)
 *		ret
 *
 * In the first case, there's only one linking point; in the second, two.
 * Linking means replacing the "mov addr,eax" instruction with a direct
 * jump to the start point of the next code fragment.
 * The parameters used are (t_ means taken, nt_ means not taken):
 *	t_ref,nt_ref	pointers to next node
 *	t_link,nt_link	addresses of the patch point
 *	t_target,nt_target jump targets, also used for unlinking
 * Since a node can be referred from many others, we need to keep
 * "back-references" in a list in order to unlink it.
 */

static void _nodeflagbackrefs(TNode *LG, unsigned short flags)
{
	/* helper routine to flag all back references:
	   if the current node uses FP then all nodes that link to
	   it must be flagged as such, which is a recursive procedure
	*/
	backref *B;

	if ((LG->flags & flags) != flags) {
	    /* only go as far back as long as flags change */
	    LG->flags |= flags;
	    for (B=LG->bkr.next; B; B=B->next)
		_nodeflagbackrefs(*B->ref, flags);
	}
}

static void linknode(TNode *LG, TNode *G, linkdesc *L, unsigned target_type)
{
	backref *B;

	// points to current node, which can't be a forever loop?
	if (L->target!=G->itree.start || !(LG->unlinked_jmp_targets & target_type) ||
	    (G->flags & F_SLFJ))
		return;

	if (L->ref!=0) {
		dbug_printf("Linker: ref at %08x busy\n",LG->itree.start);
		leavedos_main(0x8102 + (target_type == TARGET_NT));
	}
	LG->unlinked_jmp_targets &= ~target_type;
	IGen IG = (IGen){.op = JMP_LINK, .mode = MPATCH|MLINK,
			 .p0 = L->target, .link = G->addr};
	CodeGen(LG->addr + L->link, LG->addr, &IG);
	L->ref = &G->mblock->bkptr;
	B = calloc(1,sizeof(backref));
	// head insertion
	B->next = G->bkr.next;
	G->bkr.next = B;
	B->ref = &LG->mblock->bkptr;
	B->branch = target_type == TARGET_T ? 'T' : 'N';
	G->nrefs++;
	if (G==LG) {
		G->flags |= F_SLFL;
		if (debug_level('e')>1) {
			e_printf("Linker: node (%p:%08x:%p) SELF link\n"
				 "\t\ttarget=%08x, %c_ref %d=%p->%p\n",
				 G,G->itree.start,G->addr,
				 L->target, B->branch, G->nrefs, L->ref, *L->ref);
		}
	}
	else if (debug_level('e')>1) {
		e_printf("Linker: previous node (%p:%08x:%p)\n"
			 "\t\tlinked to (%p:%08x:%p)\n"
			 "\t\ttarget=%08x, %c_ref %d=%p->%p\n",
			 LG,LG->itree.start,LG->addr,
			 G,G->itree.start,G->addr,
			 L->target, B->branch, G->nrefs, L->ref, *L->ref);
	}
	_nodeflagbackrefs(LG, G->flags);
	if (debug_level('e')>8) {
		backref *bk = G->bkr.next;
#ifdef DEBUG_LINKER
		if (bk==NULL) {
			dbug_printf("bkr null\n");
			leavedos_main(0x8108 + (target_type == TARGET_NT));
		}
#endif
		while (bk) { dbug_printf("bkref=%c%p->%p\n",bk->branch,
			bk->ref,*bk->ref); bk=bk->next; }
	}
}

void NodeLinker(TNode *LG, TNode *G)
{
#if PROFILE >= 2
	hitimer_t t0 = 0;
#endif

#if !defined(SINGLESTEP)
	if (!UseLinker)
#endif
	    return;

#if PROFILE >= 2
	if (debug_level('e')) t0 = GETTSC();
#endif
	if (debug_level('e')>8 && LG) e_printf("NodeLinker: %08x->%08x\n",LG->itree.start,G->itree.start);

	if (LG && LG->alive>0 && LG->unlinked_jmp_targets) {	// node ends with links
		linknode(LG, G, &LG->clink_t, TARGET_T);
		linknode(LG, G, &LG->clink_nt, TARGET_NT);
	}
#if PROFILE >= 2
	if (debug_level('e')) LinkTime += (GETTSC() - t0);
#endif
}

static void unlinknode(TNode *G, linkdesc *T, char branch)
{
	if (!T->ref) return;

	TNode *H = *T->ref;
	backref *Bq = &H->bkr;
	backref *B  = H->bkr.next;
	if (debug_level('e')>2) e_printf("Unlink fwd %c ref to node %p(%08x)\n",
					 branch, H, H->itree.start);
	while (B) {
		if (*B->ref==G) {
			Bq->next = B->next;
			H->nrefs--;
			free(B);
			break;
		}
		Bq = B;
		B = B->next;
	}
	if (B==NULL) {	// not found...
		dbug_printf("Unlinker: FW %c ref error\n", branch);
		leavedos_main(0x8111 + (branch == 'N'));
	}
	T->ref = NULL;
}

static void NodeUnlinker(TNode *G)
{
	linkdesc *T_t = &G->clink_t;
	linkdesc *T_nt = &G->clink_nt;
	backref *B = G->bkr.next;
#if PROFILE >= 2
	hitimer_t t0 = 0;
#endif

#if !defined(SINGLESTEP)
	if (!UseLinker)
#endif
	    return;
#if PROFILE >= 2
	if (debug_level('e')) t0 = GETTSC();
#endif
	// unlink backward references (from other nodes to the current
	// node)
	if (debug_level('e')>8)
	    e_printf("Unlinker: bkr.next=%p\n",B);
	while (B) {
	    backref *b2 = B;
	    if (B->branch=='T' || B->branch=='N') {
		TNode *H = *B->ref;
		unsigned target_type;
		linkdesc *L;
		if (B->branch=='T') {
			target_type = TARGET_T;
			L = &H->clink_t;
		}
		else {
			target_type = TARGET_NT;
			L = &H->clink_nt;
		}
		if (debug_level('e')>2) e_printf("Unlinking %c ref from node %p(%08x) to %08x\n",
			B->branch, H, L->target, G->itree.start);
		if (L->target != G->itree.start) {
		    dbug_printf("Unlinker: BK %c ref error t=%08x k=%08x\n",
			B->branch, L->target, G->itree.start);
		    leavedos_main(0x8110);
		}
		IGen IG = (IGen){.op = JMP_LINK, .mode = MPATCH,
				 .p0 = L->target, .p1 = H->itree.start};
		CodeGen(H->addr + L->link, H->addr, &IG);
		L->ref = NULL; H->unlinked_jmp_targets |= target_type;
		G->nrefs--;
	    }
	    else {
		e_printf("Invalid unlink [%c] ref %p from node ?(?) to %08x\n",
			B->branch, B->ref, G->itree.start);
		leavedos_main(0x8116);
	    }
	    B = B->next;
	    free(b2);
	}

	if (G->nrefs) {
	    dbug_printf("Unlinker: nrefs error\n");
	    leavedos_main(0x8115);
	}

	// unlink forward references (from the current node to other
	// nodes), which are backward refs for the other nodes
	if (debug_level('e')>8)
	    e_printf("Unlinker: refs=T%p N%p\n",T_t->ref,T_nt->ref);
	unlinknode(G, T_t, 'T');
	unlinknode(G, T_nt, 'N');
	G->nrefs = 0;
	memset(T_t, 0, sizeof(linkdesc));
	memset(T_nt, 0, sizeof(linkdesc));
	G->unlinked_jmp_targets = 0;
	memset(&G->bkr, 0, sizeof(backref));
#if PROFILE >= 2
	if (debug_level('e')) LinkTime += (GETTSC() - t0);
#endif
}

/////////////////////////////////////////////////////////////////////////////

#ifdef DEBUG_LINKER

static void checklink(const TNode *G, const linkdesc *L, char branch)
{
  if (!L->link) return;

  const unsigned char *p = ((unsigned char *)L->link) - 1;
  if (L->ref) {
	    const TNode *GL = *L->ref;
	    if (debug_level('e')>5)
		e_printf("  %c: ref=%p link=%p\n",
			 branch,GL,L->link);
	    if ((*p!=0xe9)&&(*p!=0xeb)&&(*p!=0x48)) {
		error("bad %c link jmp\n", branch); goto nquit;
	    }
	    if (debug_level('e')>5)
		e_printf("  %c: links to %p at %08x with jmp %08x\n",branch,GL,GL->key,
		*L->link);
	    const backref *B = GL->bkr.next;
	    if ((B==NULL) || (GL->nrefs < 1)) {
		error("bad backref B=%p n=%d\n",B,GL->nrefs);
		goto nquit;
	    }
	    int n = 0;
	    int brt = 0;
	    while (B) {
		if (B->ref==&G->mblock->bkptr) {
		    n++;
		    brt += B->branch;
		    if (debug_level('e')>5) e_printf("  %c: backref %d from %p\n",branch,n,GL);
		}
		B = B->next;
	    }
	    if (n < 1 || n > 2 || (n == 2 && brt != 'N' + 'T')) {
		error("0 or >1 backrefs1 (%i)\n", n); goto nquit;
	    }
  }
  else {
	    if (*p!=0xb8) {
		error("bad %c link jmp\n", branch); goto nquit;
	    }
  }
  return;
nquit:
  leavedos_main(0x9143);
}

static void CheckLinks(void)
{
  TNode *G = &CollectTree.root;

  for (;;) {
    /* walk to next node */
    G = NEXTNODE(G);
    if (G == &CollectTree.root) {
	e_printf("DEBUG: node link check ok\n");
	return;
    }
    if (G->alive <= 0) {
	e_printf("Node %p invalidated\n",G);
	continue;
    }
    if (debug_level('e')>5) e_printf("Node %p at %08x selfr=%p\n",G,G->itree.start,
	G->mblock->bkptr);
    if (G->mblock->bkptr != G) {
	error("bad selfref\n"); goto nquit;
    }
    checklink(G, &G->clink_t, 'T');
    checklink(G, &G->clink_nt, 'N');
  }
nquit:
  leavedos_main(0x9143);
}

#endif // DEBUG_LINKER

#ifdef DEBUG_TREE

static void DumpTree (FILE *fd)
{
  TNode *G = &CollectTree.root;
  linkdesc *L;
  backref *B;
  int nn;

  if (fd==NULL) return;
  fprintf(fd,"\n== BOT ========= %6d nodes =============================\n",ninodes);
  nn = 0;

  while (nn < 10000) {		// sorry,only 4 digits available
    /* walk to next node */
    G = NEXTNODE(G);
    if (G == &CollectTree.root) {
	fprintf(fd,"\n== EOT ====================================================\n");
	fflush(fd);
	return;
    }
    fprintf(fd,"\n-----------------------------------------------------------\n");
    if (G->alive <= 0) {
	fprintf(fd,"%04d Node %p invalidated\n",nn,G);
	nn++;
	continue;
    }
    fprintf(fd,"%04d Node %p at %08x..%08x mblock=%p flags=%#x\n",
	nn,G,G->itree.start,G->itree.last,G->mblock,G->flags);
    fprintf(fd,"     AVL (%p:%p),%d,%d,%d,%d\n",G->link[0],G->link[1],
		G->bal,G->cache,G->pad,G->rtag);
    fprintf(fd,"     source:     instr=%d, len=%#x\n",G->seqnum,G->itree.last-G->itree.start+1);
    fprintf(fd,"     translated: len=%#x\n",G->len);
    L = &G->clink_t;
    fprintf(fd,"     LINK refs=%d\n",G->nrefs);
    if (L->link) {
	fprintf(fd,"         T ref=%p patch=%08x at %p\n",L->ref,
		L->target,L->link);
	L = &G->clink_nt;
	if (L->link) {
	    fprintf(fd,"         N ref=%p patch=%08x at %p\n",L->ref,
		L->target,L->link);
	}
    }
    if (G->nrefs) {
	B = G->bkr.next;
	while (B) {
	    fprintf(fd,"         bkref %c -> %p\n",B->branch,B->ref);
	    B = B->next;
	}
    }
    if (G->addr && G->pmeta) {
	int i, j, k;
	unsigned char *p = G->addr;
	Addr2Pc *AP = G->pmeta;
	for (i=0; i<G->seqnum; i++) {
	    fprintf(fd,"     %08x:%p",(G->itree.start+AP->dnpc),G->addr+AP->daddr);
	    k = 0;
	    for (j=0; j<(AP[1].daddr-AP->daddr); j++) {
		fprintf(fd," %02x",*p++); k++;
		if (k>=16) {
		    fprintf(fd,"\n                      "); k=0;
		}
	    }
	    fprintf(fd,"\n");
	    AP++;
	}
	fprintf(fd,"             :%p",G->addr+AP->daddr);
	k = 0;
	for (j=AP->daddr; j<G->len; j++) {
	    fprintf(fd," %02x",*p++); k++;
	    if (k>=16) {
		fprintf(fd,"\n                      "); k=0;
	    }
	}
	fprintf(fd,"\n");
    }
    fflush(fd);
    nn++;
  }
}

#endif // DEBUG_TREE

static int TraverseAndClean(void)
{
  int cnt = 0;
  IntervalTreeNode *p;
  TNode *G;
#if PROFILE >= 2
  hitimer_t t0 = 0;

  if (debug_level('e')) t0 = GETTSC();
#endif

  if (Traverser == NULL) {
      Traverser = interval_tree_iter_first(&ITreeRoot, 0, 0xffffffff);
      if (Traverser == NULL) return 0;
  }

  /* walk to next node */
  p = interval_tree_iter_next(Traverser, 0, 0xffffffff);
  if (p == NULL)
      p = interval_tree_iter_first(&ITreeRoot, 0, 0xffffffff);

  G = container_of(Traverser, TNode, itree);
  if ((G->addr != NULL) && (G->alive>0)) {
      G->alive -= AGENODE;
      if (G->alive <= 0) {
	if (debug_level('e')>2) e_printf("TraverseAndClean: node at %08x decayed\n",G->itree.start);
      }
  }
  if ((G->addr == NULL) || (G->alive<=0)) {
      if (debug_level('e')>2) e_printf("Delete node %08x\n",G->itree.start);
      e_unmarkpage(G->itree.start, G->itree.last - G->itree.start + 1);
      NodeUnlinker(G);
      interval_tree_remove(&G->itree, &ITreeRoot);
      dlfree(G->mblock);
      free(G);
      cnt++;
  }
  else {
      if (debug_level('e')>3)
	e_printf("TraverseAndClean: node at %08x of %d life=%d\n",
		G->itree.start,ninodes,G->alive);
  }
  Traverser = p;
#if PROFILE >= 2
  if (debug_level('e')) CleanupTime += (GETTSC() - t0);
#endif
  return cnt;
}

/*
 * Add a node to the collector tree.
 * The code is linearly stored in the CodeBuf and its associated structures
 * are in the InstrMeta array. We allocate a buffer and copy the code, then
 * we copy the sequence data from the head element of InstrMeta. In this
 * process we lose all the correspondences between original code and compiled
 * code addresses. At the end, we reset both CodeBuf and InstrMeta to prepare
 * for a new sequence.
 */
TNode *Move2Tree(IMeta *I0, CodeBuf *GenCodeBuf)
{
  TNode *nG = NULL;
#if PROFILE >= 2
  hitimer_t t0 = 0;
  if (debug_level('e')) t0 = GETTSC();
#endif
  int key;
  int nap;
  IMeta *I;
  IGen *IG;
  int i, apl=0;
  Addr2Pc *ap;
  CodeBuf *mallmb;
  void **cp;
  unsigned int op;

  key = I0->npc;

  nG = calloc(1, sizeof(TNode));
  if (nG==NULL) {
    leavedos_main(0x8201);
  }
  pthread_mutex_lock(&trees_mtx);
  nG->itree.start = key;
  nG->itree.last = key + I0->seqlen - 1;
  interval_tree_insert(&nG->itree, &ITreeRoot);
  nG->alive = NODELIFE(nG);
  pthread_mutex_unlock(&trees_mtx);

  /* transfer info from first node of the Meta list to our new node */
  nG->seqnum = I0->ncount;
#if PROFILE
  if (debug_level('e')) if (nG->len > MaxNodeSize) MaxNodeSize = nG->len;
#endif
  nG->len = I0->totlen;
  nG->flags = I0->flags;
  __atomic_store_n(&findtree_cache[key&FINDTREE_CACHE_HASH_MASK], nG,
		   __ATOMIC_RELAXED);

  /* allocate the extra memory used by the node. This includes the
   * translated code plus the table of correspondences between source
   * and translated addresses.
   * The first longword of the memory block is special; it stores a
   * back-pointer to the node. This because nodes can be moved in
   * memory when rebalancing the AVL tree, while we need absolute and
   * constant memory references.
   * The second longword is equal to its own address. Guess why.
   * After that come the offset table, then the code.
   */
  nap = nG->seqnum+1;
  mallmb = GenCodeBuf;
  nG->mblock = GenCodeBuf;
  nG->mblock->bkptr = nG;
  cp = &nG->mblock->selfptr;
  *cp = cp;
  nG->pmeta = mallmb->meta;
  if (nG->pmeta==NULL) leavedos_main(0x504d45);
  nG->addr = (unsigned char *)&mallmb->meta[nap];

  /* setup structures for inter-node linking */
  nG->unlinked_jmp_targets = 0;
  nG->clink_nt.link = nG->clink_t.link = 0;
  IG = &I0[CurrIMeta].gen[I0[CurrIMeta].ngen-1];
  op = IG->op;
  if (op == JMP_LINK) {
    nG->clink_t.link = IG->p2;
    nG->clink_t.target = IG->p0;
    nG->unlinked_jmp_targets |= TARGET_T;
    if (I0[CurrIMeta].ngen > 1 && (IG-1)->op == JMP_LINK) {
      IG--;
      nG->clink_nt.link = IG->p2;
      nG->clink_nt.target = IG->p0;
      nG->unlinked_jmp_targets |= TARGET_NT;
    }
    if ((debug_level('e')>3))
	dbug_printf("Link %d: %x:%08x\n",op,
		nG->clink_nt.link,
		((nG->unlinked_jmp_targets & TARGET_NT)? nG->clink_nt.target:0));
  }

  /* setup source/xlated instruction offsets */
  ap = nG->pmeta;
  I = I0;
  for (i=0; i<nG->seqnum; i++) {
	ap->daddr = I->daddr;
	apl = ap->daddr + I->len;
	ap->dnpc  = I->npc - I0->npc;
	if (debug_level('e')>8)
	    e_printf("Pmeta %03d: %p(%04x):%08x(%04x)\n",i,
		nG->addr+ap->daddr,ap->daddr,I->npc,ap->dnpc);
	ap++, I++;
  }
  ap->daddr = apl;
  if (debug_level('e')>8) e_printf("Pmeta %03d:         (%04x)\n",i,apl);

#ifdef DEBUG_LINKER
  CheckLinks();
#endif
  CurrIMeta = -1;
  memset(&InstrMeta[0],0,sizeof(IMeta));
#if PROFILE >= 2
  if (debug_level('e')) AddTime += (GETTSC() - t0);
#endif
  return nG;
}

void tree_gc(void)
{
  int i;
  if (ninodes > NodeLimit) {
	for (i=0; i<CreationIndex; i++) TraverseAndClean();
  }
}

static TNode *FindTree_tail(int key)
{
  IntervalTreeNode *I;
  TNode *G;
#if PROFILE >= 2
  hitimer_t t0 = 0;
  if (debug_level('e')) t0 = GETTSC();
#endif
  I = interval_tree_iter_first(&ITreeRoot, key, key);
  G = container_of(I, TNode, itree);

  if (G->addr && (G->alive>0) && G->itree.start == key) {
	if (debug_level('e')>3) e_printf("Found key %08x\n",key);
	G->alive = NODELIFE(G);
#if PROFILE
	if (debug_level('e')) {
	    NodesFound++;
#if PROFILE >= 2
	    SearchTime += (GETTSC() - t0);
#endif
	}
#endif
	return G;
  }

#if PROFILE >= 2
  if (debug_level('e')) SearchTime += (GETTSC() - t0);
#endif

  if (debug_level('e')) {
    if (debug_level('e')>4) e_printf("Not found key %08x\n",key);
#if PROFILE
    NodesNotFound++;
#endif
  }
  return NULL;
}

TNode *FindTree(int key)
{
  TNode *I;

  if (TheCPU.sigprof_pending) {
	CollectStat();
	TheCPU.sigprof_pending = 0;
  }

  /* fast path: using cache indexed by low 12 bits of PC:
     ~99.99% success rate */
  I = __atomic_load_n(&findtree_cache[key&FINDTREE_CACHE_HASH_MASK],
		      __ATOMIC_RELAXED);
  if (I && (I->alive>0) && (I->itree.start==key)) {
	if (debug_level('e')) {
	    if (debug_level('e')>4)
		e_printf("Found key %08x via cache\n", key);
#if PROFILE
	    NodesFastFound++;
#endif
	}
	I->alive = NODELIFE(I);
	return I;
  }
  if (!e_querymark(key, 1))
	return NULL;

  pthread_mutex_lock(&trees_mtx);
  I = FindTree_tail(key);
  pthread_mutex_unlock(&trees_mtx);
  if (I) {
	__atomic_store_n(&findtree_cache[key&FINDTREE_CACHE_HASH_MASK], I,
			 __ATOMIC_RELAXED);
  }
  return I;
}


/////////////////////////////////////////////////////////////////////////////
/*
 * We come here:
 *   a) from a fault on a protected memory page. A page is protected
 *	when code has been found on it. In this case, len is zero.
 *   b) from a disk read, no matter if the pages were protected or not.
 *	When we read something from disk we must mark as dirty anything
 *	present on the memory we are going to overwrite. In this case,
 *	len is greater than 0.
 * Too bad the smallest memory unit is a 4k page; DOS programs used to
 * be quite small. It is not unusual to find code and data/stack on the
 * same 4k page.
 *
 */

static int BreakNode(TNode *G, unsigned char *eip)
{
  /* if the current eip is in *any* chunk of code that is deleted
     (not just the one written to)
     then we need to break the node immediately to go back to
     the interpreter; otherwise the remaining chunk (that does
     not officially exist anymore) that the SIGSEGV or patched
     call returns to may write to the current unprotected page.
  */
  Addr2Pc *A = G->pmeta;
  int ebase;
  unsigned char *p;
  int i;
  unsigned char *ahE = G->addr + G->len;

  if (eip && ADDR_IN_RANGE(eip,G->addr,ahE)) {
    if (debug_level('e')>1)
      e_printf("### Node self hit %p->%p..%p\n",
	       eip,G->addr,ahE);
  } else {
    return 0;
  }

  ebase = eip - G->addr;
  for (i=0; i<G->seqnum; i++) {
    if (A->daddr >= ebase) {		// found following instr
	TheCPU.err = EXCP_BREAKNODE;
	BrokenNode = G;
	/* Exclude last instruction, as there is no need to break
	 * node after last instruction (it ends there anyway). */
	if (i == G->seqnum) return 1;
	IGen IG = (IGen){.op = JMP_TAILCODE, .p0 = G->itree.start + A->dnpc};
	p = G->addr + A->daddr;		// translated IP of following instr
	CodeGen(p, G->addr, &IG);
	if (debug_level('e')>1)
		e_printf("============ Force node closing at %08x(%p)\n",
			 (G->itree.start+A->dnpc),p);
	return 1;
    }
    A++;
  }
  e_printf("============ Node %08x break failed\n",G->itree.start);
  return 0;
}

void RemoveNode(TNode *G)
{
  interval_tree_remove(&G->itree, &ITreeRoot);
  __atomic_store_n(&findtree_cache[G->itree.start&FINDTREE_CACHE_HASH_MASK],
		   NULL, __ATOMIC_RELAXED);
  e_unmarkpage(G->itree.start, G->itree.last - G->itree.start + 1);
  NodeUnlinker(G);
  dlfree(G->mblock);
  free(G);
}

int InvalidateNodeRange(int al, int len, unsigned char *eip)
{
  TNode *G;
  int ah;
  int cleaned = 0;
#if PROFILE >= 2
  hitimer_t t0 = 0;

  if (debug_level('e')) t0 = GETTSC();
#endif
  ah = al + len - 1;
  if (debug_level('e')>1) dbug_printf("Invalidate area %08x..%08x\n",al,ah+1);

  pthread_mutex_lock(&trees_mtx);
  IntervalTreeNode *p = interval_tree_iter_first(&ITreeRoot, al, ah);

  /* walk tree in ascending, hopefully sorted, address order */
  for (;;) {
      IntervalTreeNode *nextp = interval_tree_iter_next(p, al, ah);
      G = container_of(p, TNode, itree);
      {
	    if (debug_level('e')>1)
		dbug_printf("Invalidated node %p at %08x\n",G,G->itree.start);
	    cleaned++;
	    if (!BreakNode(G, eip))
		RemoveNode(G);
      }
      p = nextp;
      if (!p) break;
  }
  pthread_mutex_unlock(&trees_mtx);
  if (debug_level('e') && e_querymark(al, len))
    error("simx86: InvalidateNodeRange did not clear all code for %#08x, len=%x\n",
	  al, len);
#if PROFILE >= 2
  if (debug_level('e')) CleanupTime += (GETTSC() - t0);
#endif
  return cleaned;
}


/////////////////////////////////////////////////////////////////////////////
static void do_invalidate(unsigned data, int cnt)
{
	cnt = PAGE_ALIGN(data + cnt) - (data & _PAGE_MASK);
	data &= _PAGE_MASK;
	InvalidateNodeRange(data, cnt, 0);
}

static void _e_invalidate(unsigned data, int cnt)
{
	/* nothing to invalidate if there are no page protections */
	if (!e_querymprotrange(data, cnt))
		return;
	if (!e_querymark(data, cnt))
		return;
	// no need to invalidate the whole page here,
	// as the page does not need to be unprotected
	InvalidateNodeRange(data, cnt, 0);
}

void e_invalidate(unsigned data, int cnt)
{
	prejit_lock();
	_e_invalidate(data, cnt);
	prejit_unlock();
}

void e_invalidate_pa(unsigned pa, int cnt)
{
    dosaddr_t addr = physaddr_to_dosaddr(pa, cnt);
    if (addr == (dosaddr_t)-1)
	return;
    e_invalidate(addr, cnt);
}

void e_invalidate_full_pa(unsigned pa, int cnt)
{
    dosaddr_t addr = physaddr_to_dosaddr(pa, cnt);
    if (addr == (dosaddr_t)-1)
	return;
    e_invalidate_full(addr, cnt);
}

/* invalidate and unprotect even if we hit only data.
 * Needed if we are about to destroy the page protection by other means.
 * Otherwise use e_invalidate() */
static void _e_invalidate_full(unsigned data, int cnt)
{
	/* nothing to invalidate if there are no page protections */
	if (!e_querymprotrange(data, cnt))
		return;
	do_invalidate(data, cnt);
}

void e_invalidate_full(unsigned data, int cnt)
{
	prejit_lock();
	_e_invalidate_full(data, cnt);
	prejit_unlock();
}

int e_invalidate_page_full(unsigned data)
{
	int cnt = PAGE_SIZE;
	data &= _PAGE_MASK;
	/* nothing to invalidate if there are no page protections */
	if (!e_querymprotrange(data, cnt))
		return 0;
	do_invalidate(data, cnt);
	return 1;
}

/////////////////////////////////////////////////////////////////////////////

int NewIMeta(int npc)
{
	int ret = 0;
#if PROFILE >= 2
	hitimer_t t0 = 0;

	if (debug_level('e')) t0 = GETTSC();
#endif
	if (CurrIMeta < MAXINODES-1) {
		// add new opcode metadata
		IMeta *I,*I0;

		CurrIMeta++;
		I = &InstrMeta[CurrIMeta];
		if (CurrIMeta==0) {		// no open code sequences
			if (debug_level('e')>2) e_printf("============ Opening sequence at %08x\n",npc);
			I0 = I;
		}
		else {
			I0 = &InstrMeta[0];
		}

		I0->ncount += 1;
		I->npc = npc;

		I->ngen = 0;
		I->flags = 0;
		ret = 1;
	}

#if PROFILE >= 2
	if (debug_level('e')) AddTime += (GETTSC() - t0);
#endif
	return ret;
}

/////////////////////////////////////////////////////////////////////////////

#ifdef SHOW_STAT
#define CST_SIZE	4096
static struct {
	long long a;
	int b,c,m,d,s;
} xCST[CST_SIZE];
#else
#define CST_SIZE	4
static int xCST[CST_SIZE];
#endif

static int cstx = 0;
static int xCS1 = 0;

void CollectStat (void)
{
	int i;
	unsigned int m = 0;
#ifdef SHOW_STAT
	int csm = config.CPUSpeedInMhz*1000;
//	xCST[cstx].a = TheCPU.EMUtime;
	xCST[cstx].s = TheCPU.sigprof_pending;
	xCST[cstx].b = ninodes;
	xCST[cstx].c = NodesParsed;
	xCST[cstx].d = NodesExecd;
	for (i=cstx-3; i<=cstx; i++) {
		if (i<0) { if (!xCS1) i=0; else i=CST_SIZE+i; }
		m += xCST[i].c;
	}
	m >>= 2;
	xCST[cstx].m = CLEAN_SPEED(FastLog2(m));
	i = cstx;
	if (debug_level('e')>1)
		e_printf("SIGPROF %04d %8d %8d(%3d) %8d %d\n",i,
			xCST[i].b,xCST[i].c,xCST[i].m,xCST[i].d,xCST[i].s);
	cstx++;
	if (cstx==CST_SIZE) {
	    if (!xCS1) xCS1=1;
	    for (i=0; i<cstx; i++) {
		dbug_printf("%04d %16Ld %8d %8d(%3d) %8d %d\n",i,(xCST[i].a/csm),
		    xCST[i].b,xCST[i].c,xCST[i].m,xCST[i].d,xCST[i].s);
	    }
	    cstx=0;
	}
#else
	xCST[cstx++] = NodesParsed;
	if (cstx==CST_SIZE) {
	    if (!xCS1) xCS1=1;
	    cstx=0;
	}
	if (xCS1) {
	    for (i=0; i<CST_SIZE; i++) m += xCST[i];	/* moving average */
	    m /= CST_SIZE;
	    m = FastLog2(m);	/* take leftmost bit index */
	    CreationIndex = CLEAN_SPEED(m);
	    CleanFreq = (8-m); if (CleanFreq<1) CleanFreq=1;
	}
	if (debug_level('e')>1)
		e_printf("SIGPROF %d n=%8d p=%8d x=%8d ix=%3d cln=%2d\n",
			TheCPU.sigprof_pending,
			ninodes,NodesParsed,NodesExecd,CreationIndex,
			CleanFreq);
#endif
	NodesParsed = NodesExecd = 0;
}


/////////////////////////////////////////////////////////////////////////////

void InitTrees(void)
{
	g_printf("InitTrees\n");

	if (debug_level('e')>1) {
	    e_printf("Root tree node at %p\n",&ITreeRoot);
	}
	NodesParsed = NodesExecd = 0;
	CleanFreq = 8;
	cstx = xCS1 = 0;
	CreationIndex = 0;
#if PROFILE
	if (debug_level('e')) {
	    MaxDepth = MaxNodes = MaxNodeSize = 0;
	    TotalNodesParsed = TotalNodesExecd = 0;
	    NodesFound = NodesFastFound = NodesNotFound = 0;
	    TreeCleanups = 0;
	}
#endif
}

void EndGen(void)
{
#ifdef SHOW_STAT
	int i;
	int csm = config.CPUSpeedInMhz*1000;
#endif
	CurrIMeta = -1;
#ifdef SHOW_STAT
	for (i=0; i<cstx; i++) {
	    dbug_printf("%04d %16Ld %8d %8d(%3d) %8d %d\n",i,(xCST[i].a/csm),
		xCST[i].b,xCST[i].c,xCST[i].m,xCST[i].d,xCST[i].s);
	}
#endif
}

/////////////////////////////////////////////////////////////////////////////
