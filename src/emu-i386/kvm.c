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
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

/*
 *  Emulate vm86() using KVM
 *  Started 2015, Bart Oldeman
 *  References: http://lwn.net/Articles/658511/
 *  plus example at http://lwn.net/Articles/658512/
 */

#include "config.h"

#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <linux/kvm.h>

#include "emu.h"
#include "cpu.h"
#include "dpmi.h"
#include "port.h"
#include "mhpdbg.h"

static int vcpufd = -1;
static struct kvm_run *run = NULL;
static struct kvm_sregs sregs;

/* Initialize KVM and memory mappings */
static void kvm_init(void)
{
  struct kvm_userspace_memory_region region = {
    .slot = 0,
    .guest_phys_addr = 0x0,
    .memory_size = LOWMEM_SIZE + HMASIZE,
    .userspace_addr = (uint64_t)(unsigned long)mem_base,
  };
  struct kvm_cpuid *cpuid;
  int kvm, vmfd, ret, mmap_size;

  kvm = open("/dev/kvm", O_RDWR | O_CLOEXEC);
  if (kvm == -1) {
    perror("KVM: error opening /dev/kvm");
    leavedos(99);
  }

  vmfd = ioctl(kvm, KVM_CREATE_VM, (unsigned long)0);
  if (vmfd == -1) {
    perror("KVM: KVM_CREATE_VM");
    leavedos(99);
  }

  /* Map guest memory: only conventional memory + HMA for now */
  ret = ioctl(vmfd, KVM_SET_USER_MEMORY_REGION, &region);
  if (ret == -1) {
    perror("KVM: KVM_SET_USER_MEMORY_REGION");
    leavedos(99);
  }

  vcpufd = ioctl(vmfd, KVM_CREATE_VCPU, (unsigned long)0);
  if (vmfd == -1) {
    perror("KVM: KVM_CREATE_VCPU");
    leavedos(99);
  }

  cpuid = malloc(sizeof(*cpuid) + 2*sizeof(cpuid->entries[0]));
  cpuid->nent = 2;
  // Use the same values as in emu-i386/simx86/interp.c
  // (Pentium 133-200MHz, "GenuineIntel")
  cpuid->entries[0] = (struct kvm_cpuid_entry) { .function = 0,
    .eax = 1, .ebx = 0x756e6547, .ecx = 0x6c65746e, .edx = 0x49656e69 };
  // family 5, model 2, stepping 12, fpu vme de pse tsc msr mce cx8
  cpuid->entries[1] = (struct kvm_cpuid_entry) { .function = 1,
    .eax = 0x052c, .ebx = 0, .ecx = 0, .edx = 0x1bf };
  ret = ioctl(vcpufd, KVM_SET_CPUID, cpuid);
  free(cpuid);
  if (ret == -1) {
    perror("KVM: KVM_SET_CPUID");
    leavedos(99);
  }

  mmap_size = ioctl(kvm, KVM_GET_VCPU_MMAP_SIZE, NULL);
  if (mmap_size == -1) {
    perror("KVM: KVM_GET_VCPU_MMAP_SIZE");
    leavedos(99);
  }
  if (mmap_size < sizeof(*run)) {
    fprintf(stderr, "KVM: KVM_GET_VCPU_MMAP_SIZE unexpectedly small\n");
    leavedos(99);
  }
  run = mmap(NULL, mmap_size, PROT_READ | PROT_WRITE, MAP_SHARED, vcpufd, 0);
  if (run == MAP_FAILED) {
    perror("KVM: mmap vcpu");
    leavedos(99);
  }

  ret = ioctl(vcpufd, KVM_GET_SREGS, &sregs);
  if (ret == -1) {
    perror("KVM: KVM_GET_SREGS");
    leavedos(99);
  }
}

/* Emulate vm86() using KVM
   Note: KVM traps much less than vm86.
   - VM86_SIGNAL comes from exiting with -1 and errno==EINTR
     we also exit with VM86_SIGNAL with IN/OUT instructions because KVM
     has already decoded them.
   - VM86_UNKNOWN only happens through the HLT instruction
   - VM86_INTx never happens: interrupts are handled using the IVT
     Revectored ints (as in src/base/async/int.c) do not work.
   - VM86_STI never happens; we need to use IF, not VIF;
     and VIP is not listened too (TODO: inject IRQs into KVM)
*/
int kvm_vm86(void)
{
  static struct kvm_regs regs;
  static struct kvm_guest_debug debug;
  static int debug_active;
  struct kvm_vcpu_events events;
  unsigned int newflags;
  int ret, vm86_ret;

  if (vcpufd == -1) {
    kvm_init();
  }
  newflags = vm86s.regs.eflags | 0x2;
  if (isset_IF())
    newflags |= IF;
  else
    newflags &= ~IF;
  if (mhpdbg.active || debug_active) {
    debug.control = 0;
    if (mhpdbg.active)
      debug.control |= KVM_GUESTDBG_ENABLE | KVM_GUESTDBG_USE_SW_BP;
    if (mhpdbg.TFpendig)
      /* need to do this for every single-step KVM_RUN */
      debug.control |= KVM_GUESTDBG_SINGLESTEP;
    if (mhpdbg.active != debug_active || mhpdbg.TFpendig)
      ioctl(vcpufd, KVM_SET_GUEST_DEBUG, &debug);
    debug_active = mhpdbg.active;
  }
  run->request_interrupt_window = isset_VIP();
  /* avoid syscalls if DOSEMU did not modify the CPU state */
  if (vcpufd == -1 ||
      regs.rip != vm86s.regs.eip ||
      regs.rax != vm86s.regs.eax ||
      regs.rbx != vm86s.regs.ebx ||
      regs.rcx != vm86s.regs.ecx ||
      regs.rdx != vm86s.regs.edx ||
      regs.rsi != vm86s.regs.esi ||
      regs.rdi != vm86s.regs.edi ||
      regs.rbp != vm86s.regs.ebp ||
      regs.rsp != vm86s.regs.esp ||
      regs.rflags != newflags) {
    regs.rip = vm86s.regs.eip;
    regs.rax = vm86s.regs.eax;
    regs.rbx = vm86s.regs.ebx;
    regs.rcx = vm86s.regs.ecx;
    regs.rdx = vm86s.regs.edx;
    regs.rsi = vm86s.regs.esi;
    regs.rdi = vm86s.regs.edi;
    regs.rbp = vm86s.regs.ebp;
    regs.rsp = vm86s.regs.esp;
    regs.rflags = newflags;
    ret = ioctl(vcpufd, KVM_SET_REGS, &regs);
    if (ret == -1) {
      perror("KVM: KVM_SET_REGS");
      leavedos(99);
    }
  }
  if (sregs.cs.selector != vm86s.regs.cs ||
      sregs.ds.selector != vm86s.regs.ds ||
      sregs.es.selector != vm86s.regs.es ||
      sregs.fs.selector != vm86s.regs.fs ||
      sregs.gs.selector != vm86s.regs.gs ||
      sregs.ss.selector != vm86s.regs.ss) {
    sregs.cs.base = vm86s.regs.cs << 4;
    sregs.cs.selector = vm86s.regs.cs;
    sregs.ds.base = vm86s.regs.ds << 4;
    sregs.ds.selector = vm86s.regs.ds;
    sregs.es.base = vm86s.regs.es << 4;
    sregs.es.selector = vm86s.regs.es;
    sregs.fs.base = vm86s.regs.fs << 4;
    sregs.fs.selector = vm86s.regs.fs;
    sregs.gs.base = vm86s.regs.gs << 4;
    sregs.gs.selector = vm86s.regs.gs;
    sregs.ss.base = vm86s.regs.ss << 4;
    sregs.ss.selector = vm86s.regs.ss;
    ret = ioctl(vcpufd, KVM_SET_SREGS, &sregs);
    if (ret == -1) {
      perror("KVM: KVM_SET_SREGS");
      leavedos(99);
    }
  }
  ret = ioctl(vcpufd, KVM_RUN, NULL);
  if (ret == -1 && errno != EINTR) {
    perror("KVM: KVM_RUN");
    leavedos(99);
  }
  vm86_ret = VM86_SIGNAL;
  if (ret == 0) {
    switch (run->exit_reason) {
    case KVM_EXIT_HLT:
      vm86_ret = VM86_UNKNOWN;
      break;
    case KVM_EXIT_IRQ_WINDOW_OPEN:
      vm86_ret = VM86_STI;
      break;
    case KVM_EXIT_DEBUG:
      vm86_ret = VM86_TRAP | (run->debug.arch.exception << 8);
      break;
    case KVM_EXIT_IO:
    {
      /* handle IO here to avoid decoding in vm86_GP_fault,
	 then return to DOSEMU using VM86_SIGNAL.
       */
      union data {
	Bit8u b[sizeof(*run)];
	Bit16u w[sizeof(*run)/2];
	Bit32u d[sizeof(*run)/4];
      } *data = (union data *)((Bit8u *)run + run->io.data_offset);
      switch(run->io.direction) {
      case KVM_EXIT_IO_IN:
	if (run->io.count == 1) {
	  switch(run->io.size) {
	  case 1:
	    data->b[0] = inb(run->io.port);
	    break;
	  case 2:
	    data->w[0] = inw(run->io.port);
	    break;
	  case 4:
	    data->d[0] = ind(run->io.port);
	    break;
	  default:
	    goto kvm_io_error;
	  }
	  break;
	}
	switch(run->io.size) {
	case 1:
	  port_rep_inb(run->io.port, data->b, 1, run->io.count);
	  break;
	case 2:
	  port_rep_inw(run->io.port, data->w, 1, run->io.count);
	  break;
	case 4:
	  port_rep_ind(run->io.port, data->d, 1, run->io.count);
	  break;
	default:
	  goto kvm_io_error;
	}
	break;
      case KVM_EXIT_IO_OUT:
	if (run->io.count == 1) {
	  switch(run->io.size) {
	  case 1:
	    outb(run->io.port, data->b[0]);
	    break;
	  case 2:
	    outw(run->io.port, data->w[0]);
	    break;
	  case 4:
	    outd(run->io.port, data->d[0]);
	    break;
	  default:
	    goto kvm_io_error;
	  }
	  break;
	}
	switch(run->io.size) {
	case 1:
	  port_rep_outb(run->io.port, data->b, 1, run->io.count);
	  break;
	case 2:
	  port_rep_outw(run->io.port, data->w, 1, run->io.count);
	  break;
	case 4:
	  port_rep_outd(run->io.port, data->d, 1, run->io.count);
	  break;
	default:
	  goto kvm_io_error;
	}
	break;
      default:
      kvm_io_error:
	fprintf(stderr, "KVM: unknown situation for KVM_EXIT_IO\n");
	leavedos(99);
      }
      break;
    }
    case KVM_EXIT_FAIL_ENTRY:
      ret = ioctl(vcpufd, KVM_GET_VCPU_EVENTS, &events);
      /* KVM errors out when we try to single-step STI instructions
         we can recover as follows */
      if (events.interrupt.shadow & KVM_X86_SHADOW_INT_STI) {
        events.interrupt.shadow &= ~KVM_X86_SHADOW_INT_STI;
        ioctl(vcpufd, KVM_SET_VCPU_EVENTS, &events);
        vm86_ret = VM86_TRAP | (1 << 8);
        break;
      }
      fprintf(stderr,
	      "KVM_EXIT_FAIL_ENTRY: hardware_entry_failure_reason = 0x%llx\n",
	      (unsigned long long)run->fail_entry.hardware_entry_failure_reason);
      leavedos(99);
    case KVM_EXIT_INTERNAL_ERROR:
      fprintf(stderr,
	      "KVM_EXIT_INTERNAL_ERROR: suberror = 0x%x\n", run->internal.suberror);
      leavedos(99);
    case KVM_EXIT_INTR:
      fprintf(stderr, "KVM_EXIT_INTR");
      leavedos(99);
    default:
      fprintf(stderr, "KVM: exit_reason = 0x%x\n", run->exit_reason);
      leavedos(99);
    }
  }

  ret = ioctl(vcpufd, KVM_GET_REGS, &regs);
  if (ret == -1) {
    perror("KVM: KVM_GET_REGS");
    leavedos(99);
  }
  vm86s.regs.eax = regs.rax;
  vm86s.regs.ebx = regs.rbx;
  vm86s.regs.ecx = regs.rcx;
  vm86s.regs.edx = regs.rdx;
  vm86s.regs.esi = regs.rsi;
  vm86s.regs.edi = regs.rdi;
  vm86s.regs.ebp = regs.rbp;
  vm86s.regs.esp = regs.rsp;
  vm86s.regs.eflags = regs.rflags;
  if (regs.rflags & IF)
    set_IF();
  else
    clear_IF();
  vm86s.regs.eip = regs.rip;
  /* KVM skips over the HLT instruction but vm86 stays there */
  if (vm86_ret == VM86_UNKNOWN) vm86s.regs.eip--;
  /* vm86 skips over the INT3 instruction but KVM stays there */
  if (vm86_ret == (VM86_TRAP | (3 << 8))) vm86s.regs.eip++;
  ret = ioctl(vcpufd, KVM_GET_SREGS, &sregs);
  if (ret == -1) {
    perror("KVM: KVM_GET_REGS");
    leavedos(99);
  }
  vm86s.regs.cs = sregs.cs.selector;
  vm86s.regs.ds = sregs.ds.selector;
  vm86s.regs.es = sregs.es.selector;
  vm86s.regs.fs = sregs.fs.selector;
  vm86s.regs.gs = sregs.gs.selector;
  vm86s.regs.ss = sregs.ss.selector;
  return vm86_ret;
}
