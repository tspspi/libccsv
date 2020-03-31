#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../include/ccsv.h"

#define RETVAL_NOCSVSUPPLIED			1
#define RETVAL_FOPENFAILED				2
#define RETVAL_TESTFAILED				3

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
	FILE* fHandle;
	enum csvError e;
	struct csvParser* lpP;
	int nextCharInt;

	printf("%s starting\n", argv[0]);

	if(argc < 2) {
		printf("Failed to supply CSV file name ...\n");
		return RETVAL_NOCSVSUPPLIED;
	}

	printf("Running CSV reader test on file %s\n", argv[1]);

	fHandle = fopen(argv[1], "r");
	if(fHandle == NULL) {
		printf("Failed to open %s\n", argv[1]);
		return RETVAL_FOPENFAILED;
	}

	/* Now create our parser ... */
	e = csvParserCreate(
		&lpP,
		CSVPARSER_FLAGS__HEADERLINE_ENABLE,
		&csvCallback_HeaderLine, NULL,
		&csvCallback_DataLine, NULL,
		&csvCallback_Error, NULL,
		NULL
	);
	if(e != csvE_Ok) {
		printf("%s:%u Failed to create parser ... error code %u\n", __FILE__, __LINE__, e);
		return RETVAL_TESTFAILED;
	} else {
		printf("%s:%u Parser created (%p)\n", __FILE__, __LINE__, (void*)lpP);
	}

	/*
		Now reading the file char by char and pushing
		into the state machine ...
	*/
	while((nextCharInt = fgetc(fHandle)) != EOF) {
		e = csvParserProcessByte(lpP, (char)nextCharInt);
		if(e != csvE_Ok) {
			printf("%s:%u Processing returns error %u\n", __FILE__, __LINE__, e);
			return RETVAL_TESTFAILED;
		}
	}
	if(!feof(fHandle)) {
		/* We did abort with an error condition, not with an EOF ... */
		printf("%s:%u Failed to access file while reading %s\n", __FILE__, __LINE__, argv[1]);
		return RETVAL_TESTFAILED;
	} else {
		e = csvParserFinish(lpP);
		if(e != csvE_Ok) {
			printf("%s:%u Finishing parser returns error %u\n", __FILE__, __LINE__, e);
			return RETVAL_TESTFAILED;
		}
	}
	fclose(fHandle);



	/* Release our parser */
	e = csvParserRelease(lpP);
	if(e != csvE_Ok) {
		printf("%s:%u Failed to create parser ... error code %u\n", __FILE__, __LINE__, e);
		return RETVAL_TESTFAILED;
	} else {
		printf("%s:%u Parser released\n", __FILE__, __LINE__);
	}

	printf("%s done\n", argv[0]);
	return 0;
}
