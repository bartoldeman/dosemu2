#
# (C) Copyright 1992, ..., 2014 the "DOSEMU-Development-Team".
#
# for details see file COPYING in the DOSEMU distribution
#

top_builddir=../../..
include $(top_builddir)/Makefile.conf


CFILES=commands.c lredir.c xmode.c emumouse.c dosdbg.c msetenv.c \
       unix.c cmdline.c builtins.c blaster.c

SFILES=generic.S
ALL=$(CFILES) $(SFILES)

OBJS=$(CFILES:.c=.o)
DEPENDS=$(CFILES:.c=.d) $(SFILES:.S=.d)

D:=$(BINPATH)/commands

COM = $(D)/generic.com
STUBSYMLINK = $(D)/bootoff.com $(D)/booton.com $(D)/ecpuon.com $(D)/ecpuoff.com $(D)/eject.com \
  $(D)/exitemu.com $(D)/speed.com $(D)/uchdir.com $(D)/ugetcwd.com $(D)/cmdline.com \
  $(D)/vgaoff.com $(D)/vgaon.com $(D)/lredir.com $(D)/emumouse.com $(D)/xmode.com $(D)/dosdbg.com \
  $(D)/unix.com $(D)/blaster.com $(D)/dpmi.com $(D)/lredir2.com

all: lib $(COM) $(STUBSYMLINK)

ifdef REALTOPDIR
include $(REALTOPDIR)/src/Makefile.common
endif

$(STUBSYMLINK): $(D)/generic.com
	ln -sf $(<F) $@

%.com.elf: %.o
	ld --section-start=.text=0x100 -e _start16 -o $@ $<

$(D)/%: %.elf
	objcopy -j .text -O binary $< $@
	chmod -x $@

install: all

clean::
	rm -f *~ *.o *.s *.out *.d *.com
