default: link

SHELL = bash
prefix ?= /usr/local

dirs:; mkdir -p $(prefix)/libexec
files = $(shell ls -d libexec/*)
link: uninstall dirs; for x in $(files); do \
	ln -s `pwd`/$$x $(prefix)/$$x; done
uninstall:; rm -rf $(addprefix $(prefix)/,$(files))

clean:
	rm -fdR out/*
