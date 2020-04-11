#include "../include/ccsv.h"
#include <stdio.h>
#include <errno.h>

#ifdef __cplusplus
    extern "C" {
#endif


enum csvError csvParserHelper_ProcessFile(
	const char* lpFilename,

	uint32_t dwFlags,

    csvParser_Callback_HeadersRead callbackHeader,
    void* lpFreeParam_Header,
    csvParser_Callback_RecordRead callbackRecord,
    void* lpFreeParam_Record,
    csvParser_Callback_Error callbackError,
    void* lpFreeParam_Error,

    struct csvSystemAPI* lpSystem
) {
	FILE* fHandle;
	enum csvError e;
	struct csvParser* lpP;
	int iNextChar;

	if(lpFilename == NULL) { return csvE_InvalidParam; }

	/*
		Open file in read access mode ...
	*/
	fHandle = fopen(lpFilename, "reb"); /* Open file for reading, set FD_CLOEXEC and read in binary mode */
	if(fHandle == NULL) {
		switch(errno) {
			case EINVAL:		return csvE_ImplementationError;
			case ENOMEM:		return csvE_OutOfMemory;
			case EACCES:		return csvE_PermissionDenied;
			default:			return csvE_Failed;
		}
	}

	/*
		Create parser
	*/
	e = csvParserCreate(
		&lpP,
		dwFlags,
		callbackHeader, lpFreeParam_Header,
		callbackRecord, lpFreeParam_Record,
		callbackError, lpFreeParam_Error,

		lpSystem
	);
	if(e != csvE_Ok) {
		fclose(fHandle);
		return e;
	}

	while((iNextChar = fgetc(fHandle)) != EOF) {
		e = csvParserProcessByte(lpP, (char)iNextChar);
		if(e != csvE_Ok) {
			csvParserRelease(lpP);
			fclose(fHandle);
			return e;
		}
	}

    if(!feof(fHandle)) {
        csvParserRelease(lpP);
        fclose(fHandle);
        return csvE_Failed;
    } else {
        fclose(fHandle);
    }

    e = csvParserFinish(lpP);
    csvParserRelease(lpP);
    return e;
}

#ifdef __cplusplus
	} /* extern "C" { */
#endif
