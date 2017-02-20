
#############################################################################
#
#          This file is managed by ocp-autoconf.
#
#  Remove it from `manage_files` in 'ocp-autoconf.config' if you want to
#  modify it manually.
#
#############################################################################

include autoconf/Makefile.config

all: ocp-build-build

install: ocp-build-install

clean: ocp-build-clean

distclean: clean ocp-distclean
	find . -name '*~' -exec rm -f {} \;

include autoconf/Makefile.rules

