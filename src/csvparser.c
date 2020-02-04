#include "../include/ccsv.h"

#include <stdlib.h>
#include <string.h>

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

    lpNewParser->sepChar                            = ',';
    lpNewParser->dwCurrentFieldIndex                = 0;

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
static inline enum csvError csvParser_FreeInternal(
    struct csvParser* lpP,
    void* lpBuffer
) {
    if(lpP == NULL) { return csvE_InvalidParam; }
    if(lpBuffer == NULL) { return csvE_Ok; }

    if(lpP->lpSystem == NULL) {
        free(lpBuffer);
    } else {
        lpP->lpSystem->free(lpP->lpSystem, lpBuffer);
    }
    return csvE_Ok;
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
static enum csvError csvParser_Collector_EventNextField(
    struct csvParser* lpParser
) {
    enum csvError e;
    unsigned long int dwSize, dwOffset;
    struct stringCollectorElement* lpPartIterator;
    char* lpCopyBuffer;

    if(lpParser == NULL) { return csvE_InvalidParam; }

    /*
        If no record is existing, create one ...
    */
    if(lpParser->lpCurrentRecords == NULL) {
        e = csvRecordCreate(&(lpParser->lpCurrentRecords), lpParser->dwFieldCount, lpParser->lpSystem);
        if(e != csvE_Ok) { return e; }
    }

    /*
        Count how many bytes we have to push into the
        "record" buffer
    */
    dwSize = 0;
    lpPartIterator = lpParser->collector.lpHead;
    while(lpPartIterator != NULL) {
        dwSize = dwSize + lpPartIterator->dwUsed;
        lpPartIterator = lpPartIterator->lpNext;
    }

    /*
        Allocate buffer ...
    */
    {
        e = csvParser_AllocInternal(lpParser, dwSize, (void**)(&lpCopyBuffer));
        if(e != csvE_Ok) { return e; }

        /*
            And copy data into temporary buffer
        */
        dwOffset = 0;
        lpPartIterator = lpParser->collector.lpHead;
        while(lpPartIterator != NULL) {
            memcpy(&(lpCopyBuffer[dwOffset]), lpPartIterator->bData, lpPartIterator->dwUsed);
            dwOffset = dwOffset + lpPartIterator->dwUsed;
            lpPartIterator = lpPartIterator->lpNext;
        }

        /*
            Push into record and release temporary buffer
        */
        e = csvRecordAppendField(&(lpParser->lpCurrentRecords), lpParser->dwCurrentFieldIndex, lpCopyBuffer, dwSize, lpParser->lpSystem);
        if(e == csvE_Ok) { lpParser->dwCurrentFieldIndex = lpParser->dwCurrentFieldIndex + 1; }
        csvParser_FreeInternal(lpParser, lpCopyBuffer);
    }
    return e;
}

static enum csvError csvParser_Event_FinishedRecord(
    struct csvParser* lpParser
) {
    return csvE_Ok;
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
        if(bByte == lpParser->sepChar) {
            /* Separation character */
            e = csvParser_Collector_EventNextField(lpParser); if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_IDLE;
            return csvE_Ok;
        } else if(bByte == 0x0D) {
            /* CR */
            lpParser->parserState = csvParserState_CR1;
            return csvE_Ok;
        } else if(bByte == 0x22) {
            /* DQUOTE */
            lpParser->parserState = csvParserState_EscapedField;
            return csvE_Ok;
        } else if((bByte == 0x20) || (bByte == 0x21) || ((bByte >= 0x23) && (bByte <= 0x2B)) || ((bByte >= 0x2D) && (bByte <= 0x7E))) {
            /* TEXTDATA */
            e = csvParser_Collector_Push(lpParser, bByte);
            if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_Field;
            return csvE_Ok;
        }
        return csvE_ParserError;
    } else if(lpParser->parserState == csvParserState_CR1) {
        if(bByte == 0x0A) {
            /* LF */
            lpParser->parserState = csvParserState_IDLE;
            lpParser->dwLineNumber = lpParser->dwLineNumber + 1;
            e = csvParser_Event_FinishedRecord(lpParser);
            return e;
        }
        return csvE_ParserError;
    } else if(lpParser->parserState == csvParserState_EscapedField) {
        if(bByte == 0x22) {
            /* DQUOTE */
            lpParser->parserState = csvParserState_Quote;
            return csvE_Ok;
        } else if((bByte == 0x20) || (bByte == 0x21) || ((bByte >= 0x23) && (bByte <= 0x2B)) || ((bByte >= 0x2D) && (bByte <= 0x7E)) || (bByte == ',') || (bByte == 0x0A) || (bByte == 0x0D)) {
            e = csvParser_Collector_Push(lpParser, bByte);
            if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_EscapedField;
            return csvE_Ok;
        }
        return csvE_ParserError;
    } else if(lpParser->parserState == csvParserState_Quote) {
        if(bByte == 0x22) {
            e = csvParser_Collector_Push(lpParser, bByte);
            if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_EscapedField;
            return csvE_Ok;
        } else if(bByte == lpParser->sepChar) {
            /* EV: Done Record TODO */
            /* Separation character */
            e = csvParser_Collector_EventNextField(lpParser); if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_IDLE;
            return csvE_Ok;
        } else if(bByte == 0x0D) {
            e = csvParser_Collector_EventNextField(lpParser); if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_CR3;
            return csvE_Ok;
        }
        return csvE_ParserError;
    } else if(lpParser->parserState == csvParserState_CR3) {
        if(bByte == 0x0A) {
            lpParser->parserState = csvParserState_IDLE;
            e = csvParser_Event_FinishedRecord(lpParser);
            return e;
        }
        return csvE_ParserError;
    } else if(lpParser->parserState == csvParserState_Field) {
        if((bByte == 0x20) || (bByte == 0x21) || ((bByte >= 0x23) && (bByte <= 0x2B)) || ((bByte >= 0x2D) && (bByte <= 0x7E))) {
            /* TEXTDATA */
            e = csvParser_Collector_Push(lpParser, bByte);
            if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_Field;
            return csvE_Ok;
        } else if(bByte == 0x0D) {
            e = csvParser_Collector_EventNextField(lpParser); if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_CR2;
            return csvE_Ok;
        } else if(bByte == lpParser->sepChar) {
            /* Separation character */
            e = csvParser_Collector_EventNextField(lpParser); if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_IDLE;
            return csvE_Ok;
        }
        return csvE_ParserError;
    } else if(lpParser->parserState == csvParserState_CR2) {
        if(bByte == 0x0A) {
            lpParser->parserState = csvParserState_IDLE;
            e = csvParser_Event_FinishedRecord(lpParser);
            return e;
        }
        return csvE_ParserError;
    } else {
        return csvE_ImplementationError; /* Undefined state ... should never happen */
    }
}
enum csvError csvParserFinish(
    struct csvParser* lpParser
) {
    return csvE_ImplementationError;
}

#ifdef cplusplus
    } /* extern "C" { */
#endif
