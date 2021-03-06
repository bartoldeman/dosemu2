/*
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
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/*
 * Purpose: handling of the dosemu-supplied utilities, AKA builtins.
 *
 * Author: Stas Sergeev
 * Some code is taken from coopthreads.c by Hans Lermen.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <ctype.h>
#include <sys/param.h>
#include "builtins.h"
#include "dos2linux.h"
#include "cpu.h"
#include "emu.h"
#include "int.h"
#include "utilities.h"
#include "lowmem.h"
#include "coopth.h"
#include "smalloc.h"
#include "plugin_config.h"

/* hope 2K is enough */
#define LOWMEM_POOL_SIZE 0x800
#define MAX_NESTING 32

static char builtin_name[9];
static smpool mp;
static char *lowmem_pool;
static int pool_used = 0;
#define current_builtin (pool_used - 1)

struct {
    char *cmd, *cmdl;
    struct param4a *pa4;
    int allocated;
    int quit;
} builtin_mem[MAX_NESTING];
#define BMEM(x) (builtin_mem[current_builtin].x)

char *com_getenv(char *keyword)
{
	struct PSP  *psp = COM_PSP_ADDR;
	char *env = SEG2LINEAR(psp->envir_frame);
	char key[128];
	int len;

	len = strlen(keyword);
	memcpy(key, keyword, len+1);
	strupperDOS(key);
	while (*env) {
		if (!strncmp(key, env, len) && (env[len] == '=')) {
			return env + len + 1;
		}
		env += strlen(env) + 1;
	}
	return 0;
}

static void do_exit(void *arg)
{
	fake_call_to(BIOSSEG, ROM_BIOS_EXIT);
}

static int load_and_run_DOS_program(char *command, char *cmdline, int quit)
{
	BMEM(pa4) = (struct param4a *)lowmem_alloc(sizeof(struct param4a));
	if (!BMEM(pa4)) return -1;

	BMEM(allocated) = 1;
	BMEM(quit) = quit;

	BMEM(cmd) = com_strdup(command);
	if (!BMEM(cmd)) {
		com_errno = 8;
		return -1;
	}
	BMEM(cmdl) = lowmem_alloc(256);
	if (!BMEM(cmdl)) {
		com_strfree(BMEM(cmd));
		com_errno = 8;
		return -1;
	}
	if (!cmdline) cmdline = "";
	snprintf(BMEM(cmdl), 256, "%c %s\r", (char)(strlen(cmdline)+1), cmdline);

	/* prepare param block */
	BMEM(pa4)->envframe = 0; // ctcb->envir_frame;
	BMEM(pa4)->cmdline = MK_FARt(DOSEMU_LMHEAP_SEG, DOSEMU_LMHEAP_OFFS_OF(BMEM(cmdl)));
	BMEM(pa4)->fcb1 = MK_FARt(COM_PSP_SEG, offsetof(struct PSP, FCB1));
	BMEM(pa4)->fcb2 = MK_FARt(COM_PSP_SEG, offsetof(struct PSP, FCB2));
	LWORD(es) = DOSEMU_LMHEAP_SEG;
	LWORD(ebx) = DOSEMU_LMHEAP_OFFS_OF(BMEM(pa4));
	/* path of programm to load */
	LWORD(ds) = DOSEMU_LMHEAP_SEG;
	LWORD(edx) = DOSEMU_LMHEAP_OFFS_OF(BMEM(cmd));

	LWORD(eax) = 0x4b00;
	real_run_int(0x21);

	return 0;
}

int com_system(const char *command, int quit)
{
	char *program = com_getenv("COMSPEC");
	char cmdline[256];

	snprintf(cmdline, sizeof(cmdline), "/C %s", command);
	if (!program) program = "\\COMMAND.COM";
	coopth_leave();
	fake_iret();
	return load_and_run_DOS_program(program, cmdline, quit);
}

int com_error(char *format, ...)
{
	int ret;
	va_list args;
	va_start(args, format);
	ret = com_vprintf(format, args);
	verror(format, args);
	va_end(args);
	return ret;
}

char * lowmem_alloc(int size)
{
	char *ptr = smalloc(&mp, size);
	if (!ptr) {
		error("builtin %s OOM\n", builtin_name);
		leavedos(86);
	}
	if (size > 1024) {
		/* well, the lowmem heap is limited, let's be polite! */
		error("builtin %s requests too much of a heap: 0x%x\n",
		      builtin_name, size);
	}
	return ptr;
}

void lowmem_free(char *p, int size)
{
	if (smget_area_size(&mp, p) != size) {
		error("lowmem_free size mismatch: found %i, requested %i, builtin=%s\n",
			smget_area_size(&mp, p), size, builtin_name);
	}
	return smfree(&mp, p);
}

char * com_strdup(char *s)
{
	struct lowstring *p;
	int len = strlen(s);
	if (len > 254) {
		error("lowstring too long: %i bytes. builtin: %s\n",
			len, builtin_name);
		len = 254;
	}

	p = (void *)lowmem_alloc(len + 1 + sizeof(struct lowstring));
	if (!p) return 0;
	p->len = len;
	memcpy(p->s, s, len);
	p->s[len] = 0;
	return p->s;
}

void com_strfree(char *s)
{
	struct lowstring *p = (void *)(s - 1);
	lowmem_free((char *)p, p->len + 1 + sizeof(struct lowstring));
}

static int com_argparse(char *s, char **argvx, int maxarg)
{
   int mode = 0;
   int argcx = 0;
   char delim = 0;
   char *p;

   p = strchr(s+1, '\r');
   if (p && ((p - (s+1)) < 128)) {
     *p = 0;
   }
   else s[1+(unsigned char)s[0]] = 0;
   s++;

   /* transform:
    *    dir/p to dir /p
    *    cd\ to cd \
    *    cd.. to cd ..
    */
   p = s + strcspn(s, "\\/. ");
   if (*p && *p != ' ' && (*p != '.' || (p[1] && strchr("\\/.", p[1])))) {
      memmove(p+1, p, s [-1] - (p - s) + 1/*NUL*/);
      *p = ' ';
      s[-1]++; /* update length */
   }

   maxarg --;
   for ( ; *s; s++) {
      if (!mode) {
         if (*s > ' ') {
            mode = 1;
            switch (*s) {
              case '"':
              case '\'':
                delim = *s;
                mode = 2;
                argvx[argcx++] = s+1;
                break;
              default:
                argvx[argcx++] = s;
                break;
            }
            if (argcx >= maxarg)
               break;
         }
      } else if (mode == 1) {
         if (*s <= ' ') {
            mode = 0;
            *s = 0;
         }
      } else {
         if (*s == delim) {
           *s = 0;
           mode = 1;
         }
      }
   }
   argvx[argcx] = 0;
   return(argcx);
}

int com_dosgetdrive(void)
{
        int ret;
        pre_msdos();
        HI(ax) = 0x19;
        call_msdos();    /* call MSDOS */
        ret = LO(ax);  /* 0=A, 1=B, ... */
        post_msdos();
        return ret;
}

int com_dossetdrive(int drive)
{
        int ret;
        pre_msdos();
        HI(ax) = 0x0e;
        LO(dx) = drive; /* 0=A, 1=B, ... */
        call_msdos();    /* call MSDOS */
        ret = LO(ax);  /* number of available logical drives */
        post_msdos();
        return ret;
}

int com_dossetcurrentdir(char *path)
{
        /*struct com_starter_seg  *ctcb = owntcb->params;*/
        char *s = com_strdup(path);

        com_errno = 8;
        if (!s) return -1;
        pre_msdos();
        HI(ax) = 0x3b;
        LWORD(ds) = DOSEMU_LMHEAP_SEG;
        LWORD(edx) = DOSEMU_LMHEAP_OFFS_OF(s);
        call_msdos();    /* call MSDOS */
        com_strfree(s);
        if (LWORD(eflags) & CF) {
                post_msdos();
                return -1;
        }
        post_msdos();
        return 0;
}

struct REGPACK regs_to_regpack(struct vm86_regs *regs)
{
	struct REGPACK regpack;

	regpack.r_ax =  regs->eax;
	regpack.r_bx =  regs->ebx;
	regpack.r_cx =  regs->ecx;
	regpack.r_dx =  regs->edx;
	regpack.r_bp =  regs->ebp;
	regpack.r_si =  regs->esi;
	regpack.r_di =  regs->edi;
	regpack.r_ds =  regs->ds;
	regpack.r_es =  regs->es;
	regpack.r_flags =  regs->eflags;

	return regpack;
}

struct vm86_regs regpack_to_regs(struct REGPACK *regpack)
{
	struct vm86_regs regs = _regs;

	regs.eax = regpack->r_ax;
	regs.ebx = regpack->r_bx;
	regs.ecx = regpack->r_cx;
	regs.edx = regpack->r_dx;
	regs.ebp = regpack->r_bp;
	regs.esi = regpack->r_si;
	regs.edi = regpack->r_di;
	regs.ds = regpack->r_ds;
	regs.es = regpack->r_es;
	regs.eflags = regpack->r_flags;

	return regs;
}

void com_intr(int intno, struct REGPACK *regpack)
{
	struct vm86_regs saved_regs = _regs;
	_regs = regpack_to_regs(regpack);

	do_int_call_back(intno);

	*regpack = regs_to_regpack(&_regs);
	_regs = saved_regs;
}


static struct com_program_entry *com_program_list = 0;

static struct com_program_entry *find_com_program(char *name)
{
	struct com_program_entry *com = com_program_list;

	while (com) {
		if (!strcmp(com->name, name)) return com;
		com = com->next;
	}
	return 0;
}

void register_com_program(char *name, com_program_type *program)
{
	struct com_program_entry *com;

	if ((com = find_com_program(name)) == 0) {
		com = malloc(sizeof(struct com_program_entry));
		if (!com) return;
		com->next = com_program_list;
		com_program_list = com;
	}
	com->name = name;
	com->program = program;
}

static char *com_getarg0(void)
{
	char *env = SEG2LINEAR(COM_PSP_ADDR->envir_frame);
	return memchr(env, 1, 0x10000) + 2;
}

int commands_plugin_inte6(void)
{
#define MAX_ARGS 63
	char *args[MAX_ARGS + 1];
	struct PSP *psp;
	struct MCB *mcb;
	struct com_program_entry *com;
	int argc;

	if (pool_used >= MAX_NESTING) {
	    com_error("Cannot invoke more than %i builtins\n", MAX_NESTING);
	    return 0;
	}
	if (!pool_used) {
	    if (!(lowmem_pool = lowmem_heap_alloc(LOWMEM_POOL_SIZE))) {
		error("Unable to allocate memory pool\n");
		return 0;
	    }
	    sminit(&mp, lowmem_pool, LOWMEM_POOL_SIZE);
	}
	pool_used++;
	BMEM(allocated) = 0;

	if (HI(ax) != BUILTINS_PLUGIN_VERSION) {
	    com_error("builtins plugin version mismatch: found %i, required %i\n",
		HI(ax), BUILTINS_PLUGIN_VERSION);
	    com_error("You should update your generic.com, ems.sys, isemu.com and other utilities\n"
		  "from the latest dosemu package!\n");
	    commands_plugin_inte6_done();
	    return 0;
	}

	psp = COM_PSP_ADDR;
	mcb = LOWMEM(SEGOFF2LINEAR(COM_PSP_SEG - 1,0));

	/* first parse commandline */
	args[0] = strdup(com_getarg0());
	strupperDOS(args[0]);
	argc = com_argparse((char *)&psp->cmdline_len, &args[1], MAX_ARGS - 1) + 1;

	/* DOS 4 and up */
	strncpy(builtin_name, mcb->name, sizeof(builtin_name) - 1);
	builtin_name[sizeof(builtin_name) - 1] = 0;
	strupperDOS(builtin_name);
	com = find_com_program(builtin_name);

	/* DOS 3.0->3.31 construct the program name from the environment */
	if(!com) {
		char *p = strrchr(args[0],'\\');
		strncpy(builtin_name, p+1, sizeof(builtin_name) - 1);
		builtin_name[sizeof(builtin_name) - 1] = 0;
		p = strchr(builtin_name, '.');
		if(p)
			*p = '\0';
		com = find_com_program(builtin_name);
	}

	if (com) {
		int err = com->program(argc, args);
		if (!err) {
			NOCARRY;
		} else {
			CARRY;
			_AL = err;
		}
	} else {
		com_error("inte6: unknown builtin: %s\n",builtin_name);
		CARRY;
		_AL = 1;
	}

	free(args[0]);

	return 1;
}

int commands_plugin_inte6_done(void)
{
	if (!pool_used)
	    return 0;
	if (BMEM(allocated)) {
	    com_strfree(BMEM(cmd));
	    lowmem_free((void *)BMEM(pa4), sizeof(struct param4a));
	    lowmem_free(BMEM(cmdl), 256);
	    if (BMEM(quit))
		coopth_set_post_handler(do_exit, NULL);
	}
	pool_used--;
	if (!pool_used) {
	    int leaked = smdestroy(&mp);
	    if (leaked)
		error("inte6_plugin: leaked %i bytes, builtin=%s\n",
		    leaked, builtin_name);
	    lowmem_heap_free(lowmem_pool);
	}
	return 1;
}
