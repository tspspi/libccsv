include ../Makefile.SUPPORTED

ifeq (,$(findstring $(OS),$(SUPPORTEDPLATFORMS)))

all:

	@echo The OS environment variable is currently set to [$(OS)]
	@echo Please set the OS environment variable to one of the following:
	@echo $(SUPPORTEDPLATFORMS)

.PHONY: all

else

include ../Makefile.$(OS)



all: ../bin/tests/test001_csvrecord$(EXESUFFIX) \
	../bin/tests/test002_csvread$(EXESUFFIX) \
	../bin/tests/test003_parserhelper01$(EXESUFFIX)

../bin/tests/test001_csvrecord$(EXESUFFIX): 001_csvrecord.c ../include/ccsv.h ../src/csvrecord.c

	-$(MKDIR) ../bin/tests

	$(CC) -L../bin/ -o ../bin/tests/test001_csvrecord$(EXESUFFIX) 001_csvrecord.c -lccsv

../bin/tests/test002_csvread$(EXESUFFIX): 002_csvread.c ../include/ccsv.h ../src/csvrecord.c ../src/csvparser.c

	-$(MKDIR) ../bin/tests

	$(CC) -L../bin/ -o ../bin/tests/test002_csvread$(EXESUFFIX) 002_csvread.c -lccsv

../bin/tests/test003_parserhelper01$(EXESUFFIX): 003_parserhelper01.c ../include/ccsv.h ../src/csvrecord.c ../src/csvparser.c ../src/parserhelper.c

	-$(MKDIR) ../bin/tests

	$(CC) -L../bin/ -o ../bin/tests/test003_parserhelper01$(EXESUFFIX) 003_parserhelper01.c -lccsv

runtests:

	@echo "----------------------------------------"
	@echo "- LIBCCSV Test001: CSV record handling -"
	@echo "----------------------------------------"
	../bin/tests/test001_csvrecord$(EXESUFFIX)
	@echo "---------------------------------------------------"
	@echo "- LIBCCSV Test002: CSV reading of valid CSV files -"
	@echo "---------------------------------------------------"
	../bin/tests/test002_csvread$(EXESUFFIX) test01.csv
	@echo "------------------------------------------------"
	@echo "- LIBCCSV Test003: Parser helper function test -"
	@echo "------------------------------------------------"
	../bin/tests/test003_parserhelper01$(EXESUFFIX) test01.csv


clean:

.PHONY: all clean runtests

endif
