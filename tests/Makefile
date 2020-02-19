include ../Makefile.SUPPORTED

ifeq (,$(findstring $(OS),$(SUPPORTEDPLATFORMS)))

all:

	@echo The OS environment variable is currently set to [$(OS)]
	@echo Please set the OS environment variable to one of the following:
	@echo $(SUPPORTEDPLATFORMS)

.PHONY: all

else

include ../Makefile.$(OS)



all: ../bin/tests/test001_csvrecord$(EXESUFFIX)

../bin/tests/test001_csvrecord$(EXESUFFIX): 001_csvrecord.c ../include/ccsv.h ../src/csvrecord.c

	$(MKDIR) ../bin/tests

	$(CC) -L../bin/ -o ../bin/tests/test001_csvrecord$(EXESUFFIX) 001_csvrecord.c -lccsv

runtests:

	../bin/tests/test001_csvrecord$(EXESUFFIX)

clean:

.PHONY: all clean runtests

endif
