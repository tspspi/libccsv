#include <stdio.h>
#include <stdlib.h>
#include "../include/ccsv.h"



#define RETVAL_OK                       0
#define RETVAL_TESTFAILED				1
#define RETVAL_NOCSVSUPPLIED            2



static enum csvError csvCallback_HeaderLine(
	struct csvParser* lpP,
	void* lpFreeParam,
	struct csvRecord* lpHeaderLine
) {
	unsigned long int i;
	enum csvError e;

	const char* lpData;
	unsigned long int dataLen;

	printf("\tHeader line callback returning ");
	printf("%lu headers\n", csvRecordGetFieldCount(lpHeaderLine));

	for(i = 0; i < csvRecordGetFieldCount(lpHeaderLine); i=i+1) {
		e = csvRecordGetField(lpHeaderLine, i, &lpData, &dataLen);
		if(e == csvE_Ok) {
			if(dataLen > 0) {
				printf("Field %lu (%lu bytes): \"%.*s\"\n", i, dataLen, (int)dataLen, lpData);
			} else {
				printf("Field %lu (0 bytes): empty\n", i);
			}
		}
	}

	return csvE_Ok;
}
static enum csvError csvCallback_DataLine(
	struct csvParser* lpP,
	void* lpFreeParam,
	struct csvRecord* lpData
) {
	const char* lpDta;
	unsigned long int dataLen;

	unsigned long int i;
	enum csvError e;

	printf("\tData line callback returning ");
	printf("%lu fields\n", csvRecordGetFieldCount(lpData));

	for(i = 0; i < csvRecordGetFieldCount(lpData); i=i+1) {
		e = csvRecordGetField(lpData, i, &lpDta, &dataLen);
		if(e == csvE_Ok) {
			if(dataLen > 0) {
				printf("Field %lu (%lu bytes): \"%.*s\"\n", i, dataLen, (int)dataLen, lpDta);
			} else {
				printf("Field %lu (0 bytes): empty\n", i);
			}
		}
	}

	/* Since we request ownership (csvE_Ok) we have to release */
	e = csvRecordRelease(lpData);

	return csvE_Ok;
}
static enum csvError csvCallback_Error(
	struct csvParser* lpP,
	void* lpFreeParam,
	enum csvError eCode,
	unsigned long int dwLineNumber
) {
	printf("\tError callback ...\n");
	printf("\t\tError %u at line %lu", eCode, dwLineNumber);
	return csvE_Ok;
}



int main(int argc, char* argv[]) {
    enum csvError e;

    printf("%s starting\n", argv[0]);
    if(argc < 2) {
		printf("Failed to supply CSV file name ...\n");
		return RETVAL_NOCSVSUPPLIED;
	}
    printf("Running CSV reader test on file %s\n", argv[1]);

    e = csvParserHelper_ProcessFile(
        argv[1],
        CSVPARSER_FLAGS__HEADERLINE_ENABLE,
		&csvCallback_HeaderLine, NULL,
		&csvCallback_DataLine, NULL,
		&csvCallback_Error, NULL,
		NULL
    );
    if(e == csvE_Ok) {
        printf("%s:%u Success\n", __FILE__, __LINE__);
        return RETVAL_OK;
    } else {
        printf("%s:%u Failed (code %u)\n", __FILE__, __LINE__, e);
        return RETVAL_TESTFAILED;
    }

}
