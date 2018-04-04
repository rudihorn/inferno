.PHONY: all install uninstall reinstall clean check

all install uninstall reinstall clean check:
	$(MAKE) -C src $@
