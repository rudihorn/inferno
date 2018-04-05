# -------------------------------------------------------------------------

# This Makefile is not distributed.

SHELL := bash
export CDPATH=

.PHONY: package check export tag opam pin unpin

# -------------------------------------------------------------------------

include Makefile

# -------------------------------------------------------------------------

# Utilities.

MD5SUM  := $(shell if command -v md5 >/dev/null 2>/dev/null ; \
                   then echo "md5 -r" ; else echo md5sum ; fi)

# -------------------------------------------------------------------------

# Distribution.

# The version number is automatically set to the current date,
# unless DATE is defined on the command line.
DATE     := $(shell /bin/date +%Y%m%d)

PROJECT  := inferno
PACKAGE  := $(PROJECT)-$(DATE)
CURRENT  := $(shell pwd)
TARBALL  := $(CURRENT)/$(PACKAGE).tar.gz

# -------------------------------------------------------------------------

# A list of files to copy without changes to the package.
#
# This does not include the src/ directory, which requires
# special treatment.

DISTRIBUTED_FILES := AUTHORS LICENSE Makefile README.md

# -------------------------------------------------------------------------

# Creating a tarball for distribution.

package:
# Make sure the correct version is installed.
	@ make -C src reinstall
# Create a directory to store the distributed files temporarily.
	@ rm -rf $(PACKAGE)
	@ mkdir -p $(PACKAGE)/src/lib
	@ cp $(DISTRIBUTED_FILES) $(PACKAGE)
	@ cp src/Makefile src/META src/_tags $(PACKAGE)/src
	@ cp src/lib/*.{ml,mli,mlpack} $(PACKAGE)/src/lib
# Set the version number into the files that mention it.
	@ echo "Setting version to $(DATE)."
	@ echo version = \"$(DATE)\" >> $(PACKAGE)/src/META
# Create the tarball.
	@ echo "Creating a tarball."
	tar --exclude-from=.gitignore -cvz -f $(TARBALL) $(PACKAGE)
	@ echo "The package $(PACKAGE).tar.gz is ready."

# -------------------------------------------------------------------------

# Checking the tarball that was created above.

check:
	@ echo "Checking the package ..."
# Create a temporary directory; extract, build, and install.
	@ TEMPDIR=`mktemp -d /tmp/$(PROJECT)-test.XXXXXX` && { \
	echo "   * Extracting. " && \
	(cd $$TEMPDIR && tar xfz $(TARBALL)) && \
	echo "   * Compiling and installing." && \
	(cd $$TEMPDIR/$(PACKAGE) && make reinstall \
	) > $$TEMPDIR/install.log 2>&1 \
		|| (cat $$TEMPDIR/install.log; exit 1) && \
	echo "   * Uninstalling." && \
	(cd $$TEMPDIR/$(PACKAGE) && make uninstall \
	) > $$TEMPDIR/uninstall.log 2>&1 \
		|| (cat $$TEMPDIR/uninstall.log; exit 1) && \
	rm -rf $$TEMPDIR ; }
	@ echo "The package $(PACKAGE) seems ready for distribution!"

# -------------------------------------------------------------------------

# Copying the tarball to my Web site.

RSYNC   := scp -p -C
TARGET  := yquem.inria.fr:public_html/$(PROJECT)/

export:
	$(RSYNC) $(TARBALL) $(TARGET)

# -------------------------------------------------------------------------

# Creating a git tag.

tag:
	git tag -a $(DATE) -m "Release $(DATE)."

# -------------------------------------------------------------------------

# Updating the opam package.

# This entry assumes that "make package" and "make export" have been
# run on the same day.

OPAM := $(HOME)/dev/opam-repository
CSUM  = $(shell $(MD5SUM) $(PROJECT)-$(DATE).tar.gz | cut -d ' ' -f 1)

opam:
# Update my local copy of the opam repository.
	@ echo "Updating local opam repository..."
	@ cd $(OPAM) && \
	  git fetch upstream && \
	  git merge upstream/master
# Create a new package, based on the last one.
	@ echo "Creating a new package description $(PROJECT)-$(DATE)..."
	@ cd $(OPAM)/packages/$(PROJECT) && \
	  cp -r `ls | grep $(PROJECT) | tail -1` $(PROJECT).$(DATE)
# Update the file "url".
	@ cd $(OPAM)/packages/$(PROJECT)/$(PROJECT).$(DATE) && \
	  rm url && \
	  echo 'archive: "http://gallium.inria.fr/~fpottier/$(PROJECT)/$(PROJECT)-$(DATE).tar.gz"' >> url && \
	  echo 'checksum: "$(CSUM)"' >> url
# Copy the file "opam" from $(PROJECT)'s repository to opam's.
	@ cp -f opam $(OPAM)/packages/$(PROJECT)/$(PROJECT).$(DATE)
# Prepare a commit.
	@ echo "Preparing a new commit..."
	@ cd $(OPAM)/packages/$(PROJECT) && \
	  git add $(PROJECT).$(DATE) && \
	  git status
# Ask for review.
	@ echo "If happy, please run:"
	@ echo "  cd $(OPAM)/packages/$(PROJECT) && git commit -a && git push && firefox https://github.com/"
	@ echo "and issue a pull request."

# -------------------------------------------------------------------------

# Pinning.

pin:
	opam pin add $(PROJECT) `pwd` -k git

unpin:
	opam pin remove $(PROJECT)
