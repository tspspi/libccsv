#include "../include/ccsv.h"

#include <stdlib.h>

#ifdef cplusplus
    extern "C" {
#endif

#define csvParserCreate__ALLOWEDFLAGS (CSVPARSER_FLAGS__QUIRKS_ALLOW_CR_LF_TERMINATION|CSVPARSER_FLAGS__QUIRKS_ALLOW_NONASCII|CSVPARSER_FLAGS__HEADERLINE_ENABLE)

enum csvError csvParserCreate(
    struct csvParser** lpParserOut,
    uint32_t dwFlags,

    csvParser_Callback_HeadersRead callbackHeader,
    void* lpFreeParam_Header,
    csvParser_Callback_RecordRead callbackRecord,
    void* lpFreeParam_Record,
    csvParser_Callback_Error callbackError,
    void* lpFreeParam_Error,

    struct csvSystemAPI* lpSystem
) {
    enum csvError e;
    struct csvParser* lpNewParser;

    if(lpParserOut == NULL) { return csvE_InvalidParam; }
    (*lpParserOut) = NULL;

    if((dwFlags & (~csvParserCreate__ALLOWEDFLAGS)) != 0) { return csvE_InvalidParam; }

    if(lpSystem == NULL) {
        lpNewParser = (struct csvParser*)malloc(sizeof(struct csvParser));
        if(lpNewParser == NULL) {
            return csvE_OutOfMemory;
        }
    } else {
        if((lpSystem->alloc == NULL) | (lpSystem->free == NULL)) { return csvE_InvalidParam; }
        e = lpSystem->alloc(lpSystem, sizeof(struct csvParser), (void**)(&lpNewParser));
        if(e != csvE_Ok) {
            return e;
        }
    }

    lpNewParser->parserState                        = csvParserState_IDLE;
    lpNewParser->detectedLineSepChar                = 0x00;
    lpNewParser->dwFlags                            = dwFlags;
    lpNewParser->callbacks.callbackHeader           = callbackHeader;
    lpNewParser->callbacks.lpFreeParam_Header       = lpFreeParam_Header;
    lpNewParser->callbacks.callbackRecord           = callbackRecord;
    lpNewParser->callbacks.lpFreeParam_Record       = lpFreeParam_Record;
    lpNewParser->callbacks.callbackError            = callbackError;
    lpNewParser->callbacks.lpFreeParam_Error        = lpFreeParam_Error;
    lpNewParser->dwLineNumber                       = 0;
    lpNewParser->lpSystem                           = lpSystem;

    (*lpParserOut) = lpNewParser;
    return csvE_Ok;
}
enum csvError csvParserRelease(
    struct csvParser* lpParser
) {
    struct csvSystemAPI* lpSystem;

    if(lpParser == NULL) {
        return csvE_InvalidParam;
    }

    if(lpParser->lpSystem == NULL) {
        free((void*)lpParser);
    } else {
        lpSystem = lpParser->lpSystem;
        lpSystem->free(lpSystem, (void*)lpParser);
    }

    return csvE_Ok;
}
enum csvError csvParserProcessByte(
    struct csvParser* lpParser,
    char bByte
) {
    return csvE_ImplementationError;
}


#ifdef cplusplus
    } /* extern "C" { */
#endif
