#
# (C) Copyright 1992, ..., 2014 the "DOSEMU-Development-Team".
#
# for details see file COPYING in the DOSEMU distribution
#

top_builddir=../../..
include $(top_builddir)/Makefile.conf

ALL_CFLAGS   += $(DL_CFLAGS)
LADSPA_LDFLAGS  += -lm -ldl

CFILES = load.c ladspa.c
OBJS=$(CFILES:.c=.o)
DEPENDS=$(CFILES:.c=.d)

ifdef USE_DL_PLUGINS
all: $(BINPATH)/bin/libplugin_ladspa.so
endif

include $(REALTOPDIR)/src/Makefile.common

ifdef USE_DL_PLUGINS
$(BINPATH)/bin/libplugin_ladspa.so: $(OBJS)
	$(CC) $(ALL_LDFLAGS) -shared -o $@ $^ $(LADSPA_LDFLAGS)
endif

install: all

realclean::
	rm -f config.log config.status configure
	rm -rf autom4te*.cache
