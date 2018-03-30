.PHONY: all install clean check

all:
	$(MAKE) -C src all

install:
	$(MAKE) -C src install

check:
	$(MAKE) -C src check

clean:
	$(MAKE) -C src clean
