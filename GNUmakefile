# -------------------------------------------------------------------------

# This Makefile is not distributed.

SHELL := bash
export CDPATH=

.PHONY: package export tag opam pin unpin

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

# The project name.
PROJECT  := inferno
# The repository URL (https).
REPO     := https://gitlab.inria.fr/fpottier/$(PROJECT)
# The archive URL (https).
ARCHIVE  := $(REPO)/repository/$(DATE)/archive.tar.gz
# The local repository directory.
PWD      := $(shell pwd)

# -------------------------------------------------------------------------

# Prepare a release.

package:
# Make sure the correct version can be installed.
	@ make -C src reinstall
# Update the version number in src/META.
	@ echo "Setting version to $(DATE)."
	@ mv src/META src/META.bak
	@ grep -v version src/META.bak > src/META
	@ echo version = \"$(DATE)\" >> src/META
	@ rm -f src/META.bak
	@ git commit -m "Update the version number." src/META

# -------------------------------------------------------------------------

# Publish a release. (Remember to commit everything first!)

export:
# Check if everything has been committed.
	@ if [ -n "$(git status --porcelain)" ] ; then \
	    echo "Now making a release..." ; \
	  else \
	    echo "Error: there remain uncommitted changes." ; \
	    git status ; \
	    exit 1 ; \
	  fi
# Create a git tag.
	@ git tag -a $(DATE) -m "Release $(DATE)."
# Upload. (This automatically makes a .tar.gz archive available on gitlab.)
	@ git push
	@ git push --tags

# -------------------------------------------------------------------------

# Updating the opam package.

# This entry assumes that "make package" and "make export" have been
# run on the same day.

OPAM := $(HOME)/dev/opam-repository
CSUM  = $(shell $(MD5SUM) $(PWD)/archive.tar.gz | cut -d ' ' -f 1)

opam:
# Get the .tar.gz archive, so as to compute its checksum.
	@ wget $(ARCHIVE)
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
	  echo 'archive: "$(ARCHIVE)"' >> url && \
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
