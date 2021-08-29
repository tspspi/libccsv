#include "../include/ccsv.h"

#include <stdlib.h>
#include <string.h>

#include <stdio.h>

#ifdef cplusplus
    extern "C" {
#endif

static inline enum csvError csvParser_AllocInternal(
    struct csvParser* lpP,
    unsigned long int dwSize,
    void** lpOut
);
static inline enum csvError csvParser_FreeInternal(
    struct csvParser* lpP,
    void* lpBuffer
);


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

    /*@ ghost lpSystem = NULL; */
    if(lpSystem == NULL) {
        lpNewParser = (struct csvParser*)malloc(sizeof(struct csvParser));
        if(lpNewParser == NULL) {
            return csvE_OutOfMemory;
        }
    } else {
        if((lpSystem->alloc == NULL) || (lpSystem->free == NULL)) { return csvE_InvalidParam; }
        e = lpSystem->alloc(lpSystem, sizeof(struct csvParser), (void**)(&lpNewParser));
        if(e != csvE_Ok) {
			/* @ghost e = csvE_OutOfMemory; */ /* ToDo: Remove this ghost code ... */
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
	struct stringCollectorElement* lpCurElement;
	struct stringCollectorElement* lpNextElement;

    if(lpParser == NULL) {
        return csvE_InvalidParam;
    }

	if(lpParser->lpHeaderRecord != NULL) { csvRecordRelease(lpParser->lpHeaderRecord); lpParser->lpHeaderRecord = NULL; }
	if(lpParser->lpCurrentRecords != NULL) { csvRecordRelease(lpParser->lpCurrentRecords); lpParser->lpCurrentRecords = NULL; }

	/* Release chain ... */
	lpCurElement = lpParser->collector.lpHead;
	while(lpCurElement != NULL) {
		lpNextElement = lpCurElement->lpNext;
		csvParser_FreeInternal(lpParser, (void*)lpCurElement);
		lpCurElement = lpNextElement;
	}
	lpParser->collector.lpHead = NULL;
	lpParser->collector.lpLast = NULL;

	csvParser_FreeInternal(lpParser, (void*)lpParser);

    return csvE_Ok;
}

/*@
    requires (lpP == \null) || (ccsvParser_ValidStructure(lpP));
    requires dwSize >= 0;
    requires (lpOut == \null) || ((lpOut != \null) && \valid(lpOut));

    ensures (\result == csvE_InvalidParam)
        || (\result == csvE_OutOfMemory)
        || (\result == csvE_Ok);

    behavior errInvalidOut:
        assumes lpOut == \null;

        assigns \nothing;

        ensures \result == csvE_InvalidParam;

    behavior errInvalidParser:
        assumes lpOut != \null;
        assumes lpP == \null;

		assigns (*lpOut);

        ensures \result == csvE_InvalidParam;
        ensures (*lpOut) == \null;
    behavior parameterOk:
        assumes lpOut != \null;
        assumes lpP != \null;

        ensures ((\result == csvE_Ok) && ((*lpOut) != \null))
                || ((\result == csvE_OutOfMemory) && ((*lpOut) == \null));

    complete behaviors;
    disjoint behaviors;
*/
static inline enum csvError csvParser_AllocInternal(
    struct csvParser* lpP,
    unsigned long int dwSize,
    void** lpOut
) {
    struct csvSystemAPI* lpSys;

    if(lpOut == NULL) { return csvE_InvalidParam; }
    (*lpOut) = NULL;
    if(lpP == NULL) { return csvE_InvalidParam; }

    lpSys = lpP->lpSystem;
    /*@ ghost lpSys = NULL; */
    if(lpSys == NULL) {
        (*lpOut) = malloc(dwSize);
        if((*lpOut) == NULL) {
            return csvE_OutOfMemory;
        } else {
            return csvE_Ok;
        }
    } else {
        return lpSys->alloc(lpSys, dwSize, lpOut);
    }
}
/*@
    requires (lpP == \null) || (ccsvParser_ValidStructure(lpP));
    requires (lpBuffer == \null) || (lpBuffer != \null);
    requires freeable: \freeable(lpBuffer);

    ensures (\result == csvE_Ok) || (\result == csvE_InvalidParam);

    behavior errNoParser:
        assumes lpP == \null;

        assigns \nothing;

        ensures \result == csvE_InvalidParam;
    behavior noBuffer:
        assumes lpP != \null;
        assumes lpBuffer == \null;

        assigns \nothing;

        ensures \result == csvE_Ok;
    behavior validBuffer:
        assumes lpP != \null;
        assumes lpBuffer != \null;

        ensures \result == csvE_Ok;
*/
static inline enum csvError csvParser_FreeInternal(
    struct csvParser* lpP,
    void* lpBuffer
) {
    struct csvSystemAPI* lpSys;

    if(lpP == NULL) { return csvE_InvalidParam; }
    if(lpBuffer == NULL) { return csvE_Ok; }

    lpSys = lpP->lpSystem;
    /*@ ghost lpSys = NULL; */
    if(lpSys == NULL) {
        free(lpBuffer);
    } else {
        lpSys->free(lpSys, lpBuffer);
    }
    return csvE_Ok;
}

/*
    The collector is simply an growable buffer that one can simply push
    bytes into. The collector simply chains a list of buffers as long as
    it's required to fit the data.

    Data is added into the collector by using
        csvParser_Collector_Push
    This function can also be called if there is no active collector,
    then it will just create the first buffer. If the current buffer is
    full a new one will be appended, etc.

    csvParser_Collector_EventNextField
    finalized the current field. This means it
    * Checks if a current record structure is present. If not it will get
      created
    * Allocates a buffer for the concatenated buffer content
    * Sets the appropriate entry in the csvRecord structure and flushes the
      collector (releases all buffers)
*/
/*@
    requires ccsvParser_ValidStructure(lpParser) || (lpParser == \null);

    behavior errNoParser:
        assumes lpParser == \null;

        assigns \nothing;

        ensures \result == csvE_InvalidParam;
    behavior newCollector:
        assumes lpParser != \null;
        assumes lpParser->collector.lpHead == \null;

        ensures ((\result == csvE_OutOfMemory) && (lpParser->collector.lpHead == \null))
            || (
                (\result == csvE_Ok)
                && (lpParser->collector.lpHead != \null)
                && (lpParser->collector.lpLast == lpParser->collector.lpHead)
                && (lpParser->collector.lpHead->lpNext == \null)
                && (lpParser->collector.lpHead->dwUsed == 1)
                && (lpParser->collector.lpHead->bData[0] == bByte)
            );
    behavior extistingCollectorAvailableSpace:
        assumes lpParser != \null;
        assumes lpParser->collector.lpHead != \null;
        assumes lpParser->collector.lpLast->dwUsed < CCSV_COLLECTOR_BATCH_SIZE;

        ensures lpParser->collector.lpLast->bData[\old(lpParser->collector.lpLast->dwUsed)] == bByte;
        ensures \old(lpParser->collector.lpLast->dwUsed)+1 == lpParser->collector.lpLast->dwUsed;
    behavior existingCollectorAppendSpace:
        assumes lpParser != \null;
        assumes lpParser->collector.lpHead != \null;
        assumes lpParser->collector.lpLast->dwUsed == CCSV_COLLECTOR_BATCH_SIZE;

        ensures lpParser->collector.lpLast->bData[0] == bByte;
        ensures lpParser->collector.lpLast->dwUsed == 1;
        ensures \old(lpParser->collector.lpLast->lpNext) == lpParser->collector.lpLast;
*/
static enum csvError csvParser_Collector_Push(
    struct csvParser* lpParser,
    char bByte
) {
    enum csvError e;
    if(lpParser == NULL) { return csvE_InvalidParam; }

    if(lpParser->collector.lpHead == NULL) {
        /* We have to allocate the first element */
        e = csvParser_AllocInternal(lpParser, sizeof(struct stringCollectorElement), (void**)(&(lpParser->collector.lpHead)));
		/*@ assert e == (csvE_Ok) || (e == csvE_OutOfMemory); */
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
			/*@ assert e == (csvE_Ok) || (e == csvE_OutOfMemory); */
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
/*@
	requires ccsvParser_ValidStructure(lpParser) || (lpParser == \null);

	behavior parserArgIsNull:
		assumes lpParser == \null;

		assigns \nothing;

		ensures \result == csvE_InvalidParam;

	behavior parserPresent:
		assumes lpParser != \null;

		requires ccsvParser_ValidStructure(lpParser);

		ensures ((\result == csvE_Ok) && ccsvParser_ValidStructure(lpParser))
			|| (\result == csvE_InvalidParam)
			|| (\result == csvE_OutOfMemory);
*/
static enum csvError csvParser_Collector_EventNextField(
    struct csvParser* lpParser
) {
    enum csvError e;
    unsigned long int dwSize, dwOffset;
    struct stringCollectorElement* lpPartIterator;
    struct stringCollectorElement* lpPartIteratorNext;
    char* lpCopyBuffer;

    if(lpParser == NULL) { return csvE_InvalidParam; }

    /*
        If no record is existing, create one ...
    */
	/*@ assert ccsvParser_ValidStructure(lpParser); */
    if(lpParser->lpCurrentRecords == NULL) {
        e = csvRecordCreate(&(lpParser->lpCurrentRecords), lpParser->dwFieldCount, lpParser->lpSystem);
		/*@ assert (e == csvE_Ok) || (e == csvE_InvalidParam) || (e == csvE_OutOfMemory); */
		/*@ assert ccsvParser_ValidStructure(lpParser); */
		lpParser->dwCurrentFieldIndex = 0;
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
        if(dwSize > 0) {
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
        } else {
            lpCopyBuffer = NULL;
        }
        /*
            Push into record and release temporary buffer
        */
        e = csvRecordAppendField(&(lpParser->lpCurrentRecords), lpParser->dwCurrentFieldIndex, lpCopyBuffer, dwSize, lpParser->lpSystem);
        if(e == csvE_Ok) {
            lpParser->dwCurrentFieldIndex = lpParser->dwCurrentFieldIndex + 1;

            /*
                Release the whole chain ...
            */
            lpPartIterator = lpParser->collector.lpHead;
            while(lpPartIterator != NULL) {
                lpPartIteratorNext = lpPartIterator->lpNext;
                csvParser_FreeInternal(lpParser, lpPartIterator);
                lpPartIterator = lpPartIteratorNext;
            }
            lpParser->collector.lpHead = NULL;
            lpParser->collector.lpLast = NULL;
        }
        if(lpCopyBuffer != NULL) {
            csvParser_FreeInternal(lpParser, lpCopyBuffer);
        }
    }
    return e;
}

/*
    The finish record function finalizes the current collector (if any),
    finalizes the current csvRecord and passes that to the callback function
    supplied by the application.
*/
/*@
	requires (lpParser == \null) || ccsvParser_ValidStructure(lpParser);

	ensures ccsvParser_ValidStructure(lpParser);
	ensures (\result == csvE_Ok)
		|| (\result == csvE_EncodingError)
		|| (\result == csvE_InvalidFieldCount)
		|| (\result == csvE_OutOfMemory)
		|| (\result == csvE_Abort);
*/
static enum csvError csvParser_Event_FinishedRecord(
    struct csvParser* lpParser
) {
	enum csvError e;
	if(lpParser == NULL) { return csvE_InvalidParam; }

	/*
		First finalize the current collector and append it's field ...
		This also clears the current collector
	*/

	e = csvParser_Collector_EventNextField(lpParser);
	if(e != csvE_Ok) {
		return e;
	}

	/*
		In case we did read the header or the *first* data line
		we'll also determine the number of columns. In any other
		case we will verify that the number of columns is the
		same as in the header / first line (if this check hasn't been
		disabled via a flag - TODO)
	*/
	if(((lpParser->dwFlags & CSVPARSER_FLAGS__HEADERLINE_ENABLE) != 0) && (lpParser->lpHeaderRecord == NULL)) {
		/* Header line */
		lpParser->lpHeaderRecord = lpParser->lpCurrentRecords;
		lpParser->lpCurrentRecords = NULL;
		lpParser->dwFieldCount = csvRecordGetFieldCount(lpParser->lpHeaderRecord);

		if(lpParser->callbacks.callbackHeader != NULL) {
			e = lpParser->callbacks.callbackHeader(lpParser, lpParser->callbacks.lpFreeParam_Header, lpParser->lpHeaderRecord);
			if(e != csvE_Ok) {
				/* We should abort processing ... signal this to our parser */
				return csvE_Abort;
			}
		}
		return csvE_Ok;
	} else {
		/*
			Data line

			If not disabled -> check the number of entries (0 -> this is an empty line
			and might be ignored if followed by EOF; not matching the header lines -> error)
		*/
		if(lpParser->dwFieldCount != 0) {
			if(lpParser->dwFieldCount != csvRecordGetFieldCount(lpParser->lpCurrentRecords)) {
				return csvE_InvalidFieldCount;
			}
		} else {
			/* This is the first line that we read so it defines the number of fields ... */
			lpParser->dwFieldCount = csvRecordGetFieldCount(lpParser->lpCurrentRecords);
			if(lpParser->dwFieldCount == 0) {
				return csvE_EncodingError;
			}
		}

		/* Count of fields looks valid, pass to callback */
		if(lpParser->callbacks.callbackRecord != NULL) {
			e = lpParser->callbacks.callbackRecord(lpParser, lpParser->callbacks.lpFreeParam_Record, lpParser->lpCurrentRecords);
			if(e != csvE_Ok) {
				/*
					Ok means the record has been transferred into the responsibility
					of the application, everything else means *we* have to release it
				*/
				csvRecordRelease(lpParser->lpCurrentRecords);
				e = csvE_Abort;
			}
		} else {
			csvRecordRelease(lpParser->lpCurrentRecords);
			e = csvE_Ok;
		}
		lpParser->lpCurrentRecords = NULL;

		return e;
	}
}

/*
    Public API
    Main parsing state-machine
*/
enum csvError csvParserProcessByte(
    struct csvParser* lpParser,
    char bByte
) {
    enum csvError e;

    if(lpParser == NULL) {
        return csvE_InvalidParam;
    }

    if((lpParser->dwFlags & CSVPARSER_FLAGS__QUIRKS_ALLOW_NONASCII) == 0) {
        if((bByte & 0x80) != 0) {
            return csvE_EncodingError;
        }
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
		if(lpParser->callbacks.callbackError != NULL) {
			lpParser->callbacks.callbackError(lpParser, lpParser->callbacks.lpFreeParam_Error, csvE_ParserError, lpParser->dwLineNumber);
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
		if(lpParser->callbacks.callbackError != NULL) {
			lpParser->callbacks.callbackError(lpParser, lpParser->callbacks.lpFreeParam_Error, csvE_ParserError, lpParser->dwLineNumber);
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
		if(lpParser->callbacks.callbackError != NULL) {
			lpParser->callbacks.callbackError(lpParser, lpParser->callbacks.lpFreeParam_Error, csvE_ParserError, lpParser->dwLineNumber);
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
            lpParser->parserState = csvParserState_CR3;
            return csvE_Ok;
        }
		if(lpParser->callbacks.callbackError != NULL) {
			lpParser->callbacks.callbackError(lpParser, lpParser->callbacks.lpFreeParam_Error, csvE_ParserError, lpParser->dwLineNumber);
		}
        return csvE_ParserError;
    } else if(lpParser->parserState == csvParserState_CR3) {
        if(bByte == 0x0A) {
            lpParser->parserState = csvParserState_IDLE;
            e = csvParser_Event_FinishedRecord(lpParser);
            return e;
        }
		if(lpParser->callbacks.callbackError != NULL) {
			lpParser->callbacks.callbackError(lpParser, lpParser->callbacks.lpFreeParam_Error, csvE_ParserError, lpParser->dwLineNumber);
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
            lpParser->parserState = csvParserState_CR2;
            return csvE_Ok;
        } else if(bByte == lpParser->sepChar) {
            /* Separation character */
            e = csvParser_Collector_EventNextField(lpParser); if(e != csvE_Ok) { return e; }
            lpParser->parserState = csvParserState_IDLE;
            return csvE_Ok;
        } else if(bByte == 0x0a) {
//					e = csvParser_Collector_EventNextField(lpParser); if(e != csvE_Ok) { return e; }
          lpParser->dwLineNumber = lpParser->dwLineNumber + 1;
          e = csvParser_Event_FinishedRecord(lpParser);
					lpParser->parserState = csvParserState_IDLE;
					return csvE_Ok;
				}
		if(lpParser->callbacks.callbackError != NULL) {
			lpParser->callbacks.callbackError(lpParser, lpParser->callbacks.lpFreeParam_Error, csvE_ParserError, lpParser->dwLineNumber);
		}
        return csvE_ParserError;
    } else if(lpParser->parserState == csvParserState_CR2) {
        if(bByte == 0x0A) {
            lpParser->parserState = csvParserState_IDLE;
            e = csvParser_Event_FinishedRecord(lpParser);
            return e;
        }
		if(lpParser->callbacks.callbackError != NULL) {
			lpParser->callbacks.callbackError(lpParser, lpParser->callbacks.lpFreeParam_Error, csvE_ParserError, lpParser->dwLineNumber);
		}
        return csvE_ParserError;
    } else {
        return csvE_ImplementationError; /* Undefined state ... should never happen */
    }
}
enum csvError csvParserFinish(
    struct csvParser* lpParser
) {
	enum csvError e;

	if(lpParser == NULL) {
		return csvE_InvalidParam;
	}

	if((lpParser->lpCurrentRecords != NULL) || (lpParser->collector.lpHead != NULL)) {
		e = csvParser_Event_FinishedRecord(lpParser);
		return e;
	}
    return csvE_Ok;
}

#ifdef cplusplus
    } /* extern "C" { */
#endif
