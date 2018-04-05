.PHONY: all install uninstall reinstall clean test

all install uninstall reinstall clean test:
	$(MAKE) -C src $@
