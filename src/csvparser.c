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
    lpNewParser->dwFieldCount                       = 0;
    lpNewParser->lpHeaderRecord                     = NULL;
    lpNewParser->lpCurrentRecords                   = NULL;
    lpNewParser->collector.lpHead                   = NULL;
    lpNewParser->collector.lpLast                   = NULL;

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

static inline enum csvError csvParser_AllocInternal(
    struct csvParser* lpP,
    unsigned long int dwSize,
    void** lpOut
) {
    if(lpOut == NULL) { return csvE_InvalidParam; }
    (*lpOut) = NULL;
    if(lpP == NULL) { return csvE_InvalidParam; }

    if(lpP->lpSystem == NULL) {
        (*lpOut) = malloc(dwSize);
        if((*lpOut) == NULL) {
            return csvE_OutOfMemory;
        } else {
            return csvE_Ok;
        }
    } else {
        return lpP->lpSystem->alloc(lpP->lpSystem, dwSize, lpOut);
    }
}

static enum csvError csvParser_Collector_Push(
    struct csvParser* lpParser,
    char bByte
) {
    enum csvError e;
    if(lpParser == NULL) { return csvE_InvalidParam; }

    if(lpParser->collector.lpHead == NULL) {
        /* We have to allocate the first element */
        e = csvParser_AllocInternal(lpParser, sizeof(struct stringCollectorElement), (void**)(&(lpParser->collector.lpHead)));
        if(e != csvE_Ok) { return e; }
        lpParser->collector.lpLast = lpParser->collector.lpHead;
        lpParser->collector.lpHead->lpNext = NULL;
        lpParser->collector.lpHead->dwUsed = 1;
        lpParser->collector.lpHead->bData[0] = bByte;
        return csvE_Ok;
    } else {
        /* We have to push or extend ... */
        if(lpParser->collector.lpLast->dwUsed == CCSV_COLLECTOR_BATCH_SIZE) {
            /* Append a new element ... */
            e = csvParser_AllocInternal(lpParser, sizeof(struct stringCollectorElement), (void**)(&(lpParser->collector.lpLast->lpNext)));
            if(e != csvE_Ok) { return e; }

            lpParser->collector.lpLast->lpNext->lpNext = NULL;
            lpParser->collector.lpLast->lpNext->dwUsed = 0;
            lpParser->collector.lpLast = lpParser->collector.lpLast->lpNext;
        }

        lpParser->collector.lpLast->bData[lpParser->collector.lpLast->dwUsed] = bByte;
        lpParser->collector.lpLast->dwUsed = lpParser->collector.lpLast->dwUsed + 1;
        return csvE_Ok;
    }
}

enum csvError csvParserProcessByte(
    struct csvParser* lpParser,
    char bByte
) {
    enum csvError e;

    if(lpParser == NULL) {
        return csvE_InvalidParam;
    }

    if(lpParser->parserState == csvParserState_IDLE) {
        /* We are reading a new line, first element (there is no cached element) */
        e = csvRecordCreate(&(lpParser->lpCurrentRecords), (lpParser->dwFieldCount != 0) ? lpParser->dwFieldCount : 1, lpParser->lpSystem);
        if(e != csvE_Ok) {
            /*
                We failed to allocate ...

                ToDo: Call error callback and either retry OR
                release everything and abort
            */
        }
    } else {
        return csvE_ImplementationError; /* Undefined state ... should never happen */
    }

    return csvE_ImplementationError;
}


#ifdef cplusplus
    } /* extern "C" { */
#endif
