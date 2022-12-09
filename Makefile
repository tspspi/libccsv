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
	src/csvparser.c \
	src/parserhelper.c

LIBHFILES=include/ccsv.h

OBJFILES=tmp/csvrecord$(OBJSUFFIX) \
	tmp/csvparser$(OBJSUFFIX) \
	tmp/parserhelper$(OBJSUFFIX)

all: dirs staticlib tests

dirs:

	-$(MKDIR) tmp
	-$(MKDIR) bin

staticlib: $(OBJFILES)

	$(ARCMD) bin/libccsv$(SLIBSUFFIX) $(OBJFILES)
	$(RANLIBCMD) bin/libccsv$(SLIBSUFFIX)

tests:

	- @$(MAKE) -C ./tests

package: staticlib

	# Create staging hierarchy
	-$(MKDIR) stage/lib
	-$(MKDIR) packages

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

framac:

	- @$(RMFILE) framacreport.csv
	frama-c -cpp-extra-args="-DFRAMAC" -wp -wp-verbose 1 -rte -wp-rte -wp-timeout 300 -wp-par 4 -wp-prop="-freeable,-allocation,-function_pointer" src/csvrecord.c -then -no-unicode -report -report-csv framacreport.csv > framacreport.txt


.PHONY: staticlib tests clean dirs framac

tmp/%$(OBJSUFFIX): src/%.c $(LIBHFILES)

	$(CCLIB) $(OPTIONS) -c -o $@ $<

endif
