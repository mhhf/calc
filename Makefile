default: link

SHELL = bash
dirs = {bin,libexec}
prefix ?= /usr/local

dirs:; mkdir -p $(prefix)/$(dirs)
files = $(shell ls -d $(dirs)/*)
link: uninstall dirs; for x in $(files); do \
	ln -s `pwd`/$$x $(prefix)/$$x; done
uninstall:; rm -rf $(addprefix $(prefix)/,$(files))

html:
	calc genparser
	rm -fdR out/html
	mkdir out/html
	cp src/html/*.html out/html/
	cp src/html/*.css out/html/
	./node_modules/webpack/bin/webpack.js src/html/main.js out/html/bundle.js

test:
	./node_modules/mocha/bin/mocha tests
