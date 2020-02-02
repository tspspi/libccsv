include Makefile.SUPPORTED

ifeq (,$(findstring $(OS),$(SUPPORTEDPLATFORMS)))

all:

	@echo The OS environment variable is currently set to [$(OS)]
	@echo Please set the OS environment variable to one of the following:
	@echo $(SUPPORTEDPLATFORMS)

.PHONY: all

else

include Makefile.$(OS)

OPTIONS=
LIBSRCFILES=src/csvrecord.c \
	src/csvparser.c

LIBHFILES=include/ccsv.h

OBJFILES=tmp/csvrecord$(OBJSUFFIX) \
	tmp/csvparser$(OBJSUFFIX)

all: staticlib tests

staticlib: $(OBJFILES)

	$(ARCMD) bin/libccsv$(SLIBSUFFIX) $(OBJFILES)

tests:

	- @$(MAKE) -C ./tests

package: staticlib

	# Create staging hierarchy
	$(MKDIR) stage/lib
	$(MKDIR) packages

	# Copy files
	$(CP) bin/libccsv$(SLIBSUFFIX) stage/lib/libccsv$(SLIBSUFFIX)

	# Create archive
	$(MKSTAGEARCHIVE)

	# Cleanup
	$(RMDIR) stage

clean:

	- @$(RMDIR) stage
	- @$(RMDIR) packages
	- @$(RMFILE) bin/*$(SLIBSUFFIX)
	- @$(RMFILE) bin/tests/test*

.PHONY: staticlib tests clean

tmp/%$(OBJSUFFIX): src/%.c $(LIBHFILES)

	$(CCLIB) $(OPTIONS) -c -o $@ $<

endif
