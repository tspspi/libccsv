#ifndef __is_included__e2db3911_45df_11ea_8fdc_b499badf00a1
#define __is_included__e2db3911_45df_11ea_8fdc_b499badf00a1 1

#ifndef CCSV_COLLECTOR_BATCH_SIZE
    #define CCSV_COLLECTOR_BATCH_SIZE           1024
#endif

#include <stdint.h>

#ifdef __cplusplus
    extern "C" {
#endif

struct csvParser;
enum csvError {
    csvE_Ok                                 = 0,

    csvE_OutOfMemory                        = 1,
    csvE_InvalidParam                       = 2,
    csvE_IndexOutOfBounds                   = 3,

    csvE_ParserError                        = 4,
	csvE_EncodingError						= 5,
	csvE_InvalidFieldCount					= 6,

	csvE_Abort								= 7,

	csvE_Failed								= 8,
    csvE_PermissionDenied                   = 9,

    csvE_ImplementationError                = 255
};

/*
    System API
*/

struct csvSystemAPI;
/*@
    requires \valid(lpSelf) || (lpSelf == \null);
    requires (\valid(lpDataOut) && (lpDataOut != \null)) || ((lpDataOut == \null) && (!\valid(lpDataOut)));
    requires dwSize >= 0;

    behavior invalidParamDataOut:
        assumes lpDataOut == \null;

        assigns \nothing;

        ensures \result == csvE_InvalidParam;
    behavior invalidParamSelf:
        assumes lpSelf == \null;
        assumes lpDataOut != \null;

        assigns (*lpDataOut);

        ensures \result == csvE_InvalidParam;
        ensures (*lpDataOut) == \null;
    behavior allocationZeroLength:
        assumes lpSelf != \null;
        assumes lpDataOut != \null;
        assumes dwSize == 0;

        ensures (\result == csvE_Ok) && ((*lpDataOut) == \null);
    behavior allocationOrNoAllocation:
        assumes lpSelf != \null;
        assumes lpDataOut != \null;
        assumes dwSize > 0;

        ensures ((\result == csvE_Ok) && ((*lpDataOut) != \null)) || ((\result == csvE_OutOfMemory) && ((*lpDataOut) == \null));
    disjoint behaviors;
    complete behaviors;
*/
/*
    Note the following would be better but is_allocable is not supported
    on current frama-c implementation ...

    behavior allocation:
        assumes can_allocate: is_allocable(dwSize);
        assumes lpSelf != \null;
        assumes lpDataOut != \null;

        assigns (*lpDataOut);

        ensures allocation: \fresh(*lpDataOut,dwSize);
        ensures ((\result == csvE_Ok) && ((*lpDataOut) != \null)) || ((\result == csvE_OutOfMemory) && ((*lpDataOut) == \null));
    behavior no_allocation:
        assumes cannot_allocate: !is_allocable(dwSize);
        assumes lpSelf != \null;
        assumes lpDataOut != \null;

        assigns (*lpDataOut) \from \nothing;
        allocates \nothing;

        ensures (*lpDataOut) == \null;
        ensures ((\result == csvE_Ok) && ((*lpDataOut) != \null)) || ((\result == csvE_OutOfMemory) && ((*lpDataOut) == \null));

*/
typedef enum csvError (*csvSystemAPI_Alloc)(
	struct csvSystemAPI*						lpSelf,
	unsigned long int							dwSize,
	void**										lpDataOut
);
/*@
    requires (\valid(lpSelf) && (lpSelf != \null)) || (lpSelf == \null);
    requires freeable: \freeable(lpObject);

    behavior validParams:
        assumes (lpSelf != \null) && (lpObject != \null);

        frees lpObject;

        ensures \result == csvE_Ok;
    behavior invalidParamSelf:
        assumes lpSelf == \null;

        ensures \result == csvE_InvalidParam;
    behavior invalidParam_Object:
        assumes (lpSelf != \null) && (lpObject == \null);

        ensures \result == csvE_Ok;

    complete behaviors;
    disjoint behaviors;
*/
typedef enum csvError (*csvSystemAPI_Free)(
	struct csvSystemAPI*						lpSelf,
	void*										lpObject
);

struct csvSystemAPI {
    csvSystemAPI_Alloc                          alloc;
    csvSystemAPI_Free                           free;
};

/*
    Record data structure

        A record inside a CSV is simply a collection of
        cells (i.e. it represents a single line). Each
        cell can be artibrarily long - the only assumption
        made in this library is that a single line fits
        into main memory.

        During the first line that gets parsed the number of
        elements gets counted for the first time so the
        resize function gets used a lot - later on this normally
        doesn't happen any more.
*/

struct csvRecord {
    unsigned long int dwFieldCount;
    unsigned long int dwUsedFieldCount;
    struct csvSystemAPI* lpSystem;

    struct {
        unsigned long int dwDataLen;
        char* lpData;
    } fields[];
};

/*@
    predicate validCCSVCsvSystem(struct csvSystemAPI *s) =
        \valid(s)
        && \valid(&(s->alloc))
        && \valid(&(s->free))
        && (s->alloc != \null)
        && (s->free != \null);
*/
/*@
    predicate validCCSVCsvRecord(struct csvRecord *s) =
        \valid(s)
        && \valid(&(s->dwFieldCount))
        && \valid(&(s->dwUsedFieldCount))
        && \valid(&(s->lpSystem))
        && (validCCSVCsvSystem(s->lpSystem) || (s->lpSystem == \null))
        && (s->dwFieldCount >= 0)
        && (s->dwUsedFieldCount >= 0)
        && (\valid(&(s->fields[0..s->dwFieldCount].lpData)))
        && (\valid(&(s->fields[0..s->dwFieldCount].dwDataLen)));
*/

/*@
    requires (lpOut == \null) || ((lpOut != \null) && \valid(lpOut));
    requires validCCSVCsvSystem(lpSystem) || (lpSystem == \null);
    requires dwInitialFieldCount >= 0;

	assigns (*lpOut);
	assigns ((*lpOut)->dwUsedFieldCount);
	assigns ((*lpOut)->dwFieldCount);
	assigns ((*lpOut)->lpSystem);
	assigns ((*lpOut)->fields[0..dwInitialFieldCount-1].dwDataLen);
	assigns ((*lpOut)->fields[0..dwInitialFieldCount-1].lpData);

    ensures (
				(\result == csvE_InvalidParam)
				|| (\result == csvE_OutOfMemory)
			) || (
				validCCSVCsvRecord(*lpOut)
            	&& (\result == csvE_Ok)
            	&& (*lpOut)->dwUsedFieldCount == 0
            	&& (*lpOut)->dwFieldCount == dwInitialFieldCount
            	&& (*lpOut)->lpSystem == lpSystem
            	&& (\forall int n; 0 <= n < dwInitialFieldCount
                    	==> ((*lpOut)->fields[n].dwDataLen == 0)
                        	&& ((*lpOut)->fields[n].lpData == \null)
                	)
        	);

    behavior invalidOutPtr:
        assumes lpOut == \null;

        assigns \nothing;

        ensures \result == csvE_InvalidParam;
    behavior invalidSystemStructure:
        assumes (lpOut != \null) && \valid(lpOut);
        assumes (lpSystem != \null) && !validCCSVCsvSystem(lpSystem);

		assigns \nothing;

        ensures (*lpOut) == \null;
        ensures \result == csvE_InvalidParam;
    behavior validNoSystem:
        assumes (lpOut != \null) && \valid(lpOut);
        assumes lpSystem == \null;

		assigns (*lpOut);
		assigns ((*lpOut)->dwUsedFieldCount);
		assigns ((*lpOut)->dwFieldCount);
		assigns ((*lpOut)->lpSystem);
		assigns ((*lpOut)->fields[0..dwInitialFieldCount-1].dwDataLen);
		assigns ((*lpOut)->fields[0..dwInitialFieldCount-1].lpData);

        ensures (*lpOut) != \null;

        ensures \valid((*lpOut));
        ensures ((\result == csvE_Ok) && ((*lpOut) != \null))
            || ((\result == csvE_OutOfMemory) && ((*lpOut) == \null));

        ensures ((*lpOut)->dwUsedFieldCount == 0) || (\result != csvE_Ok);
        ensures ((*lpOut)->dwFieldCount == dwInitialFieldCount) || (\result != csvE_Ok);

        ensures \forall int n; 0 <= n < dwInitialFieldCount
            ==> ((*lpOut)->fields[n].dwDataLen == 0) && ((*lpOut)->fields[n].lpData == \null);

        ensures ((*lpOut)->lpSystem == \null) || (\result != csvE_Ok);
        ensures \valid(&(*lpOut)) || (\result != csvE_Ok);
        ensures \valid(&((*lpOut)->dwUsedFieldCount)) || (\result != csvE_Ok);
        ensures \valid(&((*lpOut)->dwFieldCount)) || (\result != csvE_Ok);
    behavior validWithSystem:
        assumes (lpOut != \null) && \valid(lpOut);
        assumes (lpSystem != \null) && \valid(lpSystem);
        assumes (lpSystem->alloc != \null) && (lpSystem->free != \null);

		assigns (*lpOut);
		assigns ((*lpOut)->dwUsedFieldCount);
		assigns ((*lpOut)->dwFieldCount);
		assigns ((*lpOut)->lpSystem);
		assigns ((*lpOut)->fields[0..dwInitialFieldCount-1].dwDataLen);
		assigns ((*lpOut)->fields[0..dwInitialFieldCount-1].lpData);

        ensures (*lpOut) != \null;
        ensures \valid((*lpOut));
        ensures ((\result == csvE_Ok) && ((*lpOut) != \null))
            || ((\result == csvE_OutOfMemory) && ((*lpOut) == \null));

        ensures ((*lpOut)->dwUsedFieldCount == 0) || (\result != csvE_Ok);
        ensures ((*lpOut)->dwFieldCount == dwInitialFieldCount) || (\result != csvE_Ok);

        ensures \forall int n; 0 <= n < dwInitialFieldCount
            ==> ((*lpOut)->fields[n].dwDataLen == 0) && ((*lpOut)->fields[n].lpData == \null);

        ensures ((*lpOut)->lpSystem != \null) || (\result != csvE_Ok);
        ensures \valid(&(*lpOut)) || (\result != csvE_Ok);
        ensures \valid(&((*lpOut)->dwUsedFieldCount)) || (\result != csvE_Ok);
        ensures \valid(&((*lpOut)->dwFieldCount)) || (\result != csvE_Ok);

    complete behaviors;
    disjoint behaviors;
*/
enum csvError csvRecordCreate(
    struct csvRecord** lpOut,
    unsigned long int dwInitialFieldCount,

    struct csvSystemAPI* lpSystem
);
/*@
    requires validCCSVCsvRecord(lpRecord) || (lpRecord == \null);

    ensures \result == csvE_Ok;

    behavior hasRecordAndSystem:
        assumes (lpRecord != \null);
        assumes (lpRecord->lpSystem != \null);

        ensures lpRecord->dwFieldCount == 0;
        ensures \forall int n; 0 <= n < lpRecord->dwFieldCount
            ==> (lpRecord->fields[n].lpData == \null)
                && (lpRecord->fields[n].dwDataLen == 0);

    behavior hasRecordAndNoSystem:
        assumes (lpRecord != \null);
        assumes (lpRecord->lpSystem == \null);

        ensures lpRecord->dwFieldCount == 0;
        ensures \forall int n; 0 <= n < lpRecord->dwFieldCount
            ==> (lpRecord->fields[n].lpData == \null)
                && (lpRecord->fields[n].dwDataLen == 0);

    behavior hasNoRecord:
        assumes (lpRecord == \null);

        assigns \nothing;

    complete behaviors;
    disjoint behaviors;
*/
enum csvError csvRecordRelease(
    struct csvRecord* lpRecord
);
/*@
    requires (lpRecordInOut == \null) ||
        (lpRecordInOut != \null) && \valid(lpRecordInOut) && (
            validCCSVCsvRecord(*lpRecordInOut)
            || (*lpRecordInOut == \null)
        );

    requires dwNewFieldCount >= 0;

    assigns (*lpRecordInOut);

    behavior noInOutPointer:
        assumes lpRecordInOut == \null;

        assigns \nothing;

        ensures \result == csvE_InvalidParam;

    behavior noInRecord:
        assumes lpRecordInOut != \null;
        assumes (*lpRecordInOut) == \null;

        assigns \nothing;

        ensures \result == csvE_InvalidParam;

    behavior shrinkRequest:
        assumes lpRecordInOut != \null;
        assumes (*lpRecordInOut) != \null;
        assumes (*lpRecordInOut)->dwUsedFieldCount > dwNewFieldCount;

        assigns \nothing;

        ensures \result == csvE_InvalidParam;

    behavior correctParameters:
        assumes lpRecordInOut != \null;
        assumes (*lpRecordInOut) != \null;
        assumes (*lpRecordInOut)->dwUsedFieldCount <= dwNewFieldCount;

        ensures
            \result != csvE_Ok
            || (
                (\result == csvE_Ok)
                && (\forall int n; 0 <= n < (*lpRecordInOut)->dwUsedFieldCount ==> ((*lpRecordInOut))->fields[n] == \old((*lpRecordInOut))->fields[n])
                && validCCSVCsvRecord(*lpRecordInOut)
            );
*/
enum csvError csvRecordResize(
    struct csvRecord** lpRecordInOut,
    unsigned long int dwNewFieldCount
);
/*@
    requires validCCSVCsvRecord(lpRecordIn) || (lpRecordIn == \null);

    assigns \nothing;

    ensures \result >= 0;

    behavior validPtr:
        assumes (lpRecordIn != \null);

        ensures \result == lpRecordIn->dwUsedFieldCount;
        ensures \result >= 0;

    behavior invalidPtr:
        assumes (lpRecordIn == \null);

        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
unsigned long int csvRecordGetFieldCount(
    struct csvRecord* lpRecordIn
);
/*@
    requires validCCSVCsvRecord(lpRecordIn) || (lpRecordIn == \null);

    assigns \nothing;

    ensures \result >= 0;

    behavior validPtr:
        assumes (lpRecordIn != \null);

        ensures \result == lpRecordIn->dwFieldCount;
        ensures \result >= 0;

    behavior invalidPtr:
        assumes (lpRecordIn == \null);

        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
unsigned long int csvRecordGetFieldCountCapacity(
    struct csvRecord* lpRecordIn
);
/*@
    requires validCCSVCsvRecord(lpRecord) || (lpRecord == \null);
    requires dwFieldIndex >= 0;
    requires (\valid(lpData_Out) && (lpData_Out != \null)) || (lpData_Out == \null);
    requires (\valid(lpDataLen_Out) && (lpDataLen_Out != \null)) || (lpDataLen_Out == \null);

    behavior invalidRecord:
        assumes !validCCSVCsvRecord(lpRecord);
        assigns (*lpData_Out);
        assigns (*lpDataLen_Out);

        ensures ((*lpData_Out) == \null) || (lpData_Out == \null);
        ensures ((*lpDataLen_Out) == 0) || (lpDataLen_Out == \null);
        ensures \result == csvE_InvalidParam;
    behavior indexOutOfBounds:
        assumes validCCSVCsvRecord(lpRecord);
        assumes dwFieldIndex >= lpRecord->dwUsedFieldCount;

        ensures ((*lpData_Out) == \null) || (lpData_Out == \null);
        ensures ((*lpDataLen_Out) == 0) || (lpDataLen_Out == \null);
        ensures \result == csvE_IndexOutOfBounds;
    behavior allValid:
        assumes validCCSVCsvRecord(lpRecord);
        assumes dwFieldIndex < lpRecord->dwUsedFieldCount;

        ensures ((*lpData_Out) == lpRecord->fields[dwFieldIndex].lpData) || (lpData_Out == \null);
        ensures ((*lpDataLen_Out) == lpRecord->fields[dwFieldIndex].dwDataLen) || (lpDataLen_Out == \null);
        ensures \result == csvE_Ok;

    complete behaviors;
    disjoint behaviors;
*/
enum csvError csvRecordGetField(
    struct csvRecord* lpRecord,
    unsigned long int dwFieldIndex,

    const char** lpData_Out,
    unsigned long int* lpDataLen_Out
);
/*@
    requires validCCSVCsvRecord(lpRecord) || (lpRecord == \null);
    requires dwFieldIndex >= 0;

    behavior invalidRecordPtr:
        assumes lpRecord == \null;
        ensures \result == csvE_InvalidParam;
    behavior outOfBOunds:
        assumes lpRecord != \null;
        assumes dwFieldIndex >= lpRecord->dwFieldCount;

        ensures \result == csvE_IndexOutOfBounds;
    behavior paramsOk:
        assumes lpRecord != \null;
        assumes dwFieldIndex < lpRecord->dwFieldCount;

        assigns lpRecord->fields[dwFieldIndex].lpData;
        assigns lpRecord->fields[dwFieldIndex].dwDataLen;

        ensures (\result == csvE_Ok) || (\result == csvE_OutOfMemory);
        ensures \valid(lpRecord->fields[dwFieldIndex].lpData) || (\result != csvE_Ok) || (lpRecord->fields[dwFieldIndex].lpData == \null);

    disjoint behaviors;
    complete behaviors;
*/
enum csvError csvRecordSetField(
    struct csvRecord* lpRecord,
    unsigned long int dwFieldIndex,

    const char* lpDataIn,
    unsigned long int dwDataLen
);
/*@
    requires validCCSVCsvRecord(*lpRecord) || (lpRecord == \null);

    requires dwFieldIndex >= 0;

    requires \valid(lpDataIn) || (lpDataIn == \null);
    requires dwDataLen >= 0;

    behavior invalidParameter:
        assumes lpRecord == \null;

        ensures \result == csvE_InvalidParam;
    behavior correctParameter:
        assumes lpRecord != \null;

        requires validCCSVCsvRecord(*lpRecord);

        ensures (validCCSVCsvRecord(*lpRecord) && \result == csvE_Ok) || (\result != csvE_Ok);
        ensures (\result == csvE_Ok) || (\result == csvE_OutOfMemory) || (\result == csvE_InvalidParam);

    complete behaviors;
    disjoint behaviors;
*/
enum csvError csvRecordAppendField(
    struct csvRecord** lpRecord,
    unsigned long int dwFieldIndex,

    const char* lpDataIn,
    unsigned long int dwDataLen,

    struct csvSystemAPI* lpSystem
);

/*
    Parser API
*/

/*
    Flags:
        CSVPARSER_FLAGS__QUIRKS_ALLOW_CR_LF_TERMINATION
            Does not enforce to allow only termination using CRLF (like stated
            in RFC4180) but also allows termination using a single CR or
            single LF (the first encountered one is threatened as line termination,
            the other one silently ignored except for payload data)
        CSVPARSER_FLAGS__QUIRKS_ALLOW_NONASCII
            This flag allows non ASCII characters inside payload and does
            not validate that only ASCII symbols are used. If this flag
            is not set the format is strictly validated against RFC4180. If
            this flag is set UTF8 or any other encoding that doesn't collide
            with the separation character and double quotation mark (any unicode
            encoding is compatible) might be used (content is copied unmodified)
        CSVPARSER_FLAGS__HEADERLINE_ENABLE
            Enabled header line processing. This allows the parser to
            detect the names of headers (they are reported separately) and
            allows applications to ask for fields by name (as well as field
            indices by name)
*/
#define CSVPARSER_FLAGS__QUIRKS_ALLOW_CR_LF_TERMINATION     0x00000001
#define CSVPARSER_FLAGS__QUIRKS_ALLOW_NONASCII              0x00000002
#define CSVPARSER_FLAGS__HEADERLINE_ENABLE                  0x80000000

enum csvParserState {
    csvParserState_IDLE                 = 0,

    csvParserState_CR1,

    csvParserState_Field,
    csvParserState_CR2,

    csvParserState_EscapedField,
    csvParserState_Quote,
    csvParserState_CR3,

    csvParserState_DONE,
};

struct csvParser;

typedef enum csvError (*csvParser_Callback_HeadersRead)(
    struct csvParser* lpParser,
    void* lpFreeParam,
	struct csvRecord* lpHeaderLine
);
typedef enum csvError (*csvParser_Callback_RecordRead)(
    struct csvParser* lpParser,
    void* lpFreeParam,
    struct csvRecord* lpData
);
typedef enum csvError (*csvParser_Callback_Error)(
    struct csvParser* lpParser,
    void* lpFreeParam,
    enum csvError eCode,
    unsigned long int dwLineNumber
);

struct stringCollectorElement {
    unsigned long int dwUsed;
    struct stringCollectorElement* lpNext;
    char bData[CCSV_COLLECTOR_BATCH_SIZE];
};

struct csvParser {
    enum csvParserState parserState;
    uint8_t detectedLineSepChar;        /* Will be set to 0x0D or 0x0A (CR or LF) as detected or 0x00 if none has been encountered till now */
    uint32_t dwFlags;                   /* Configured flags */
    unsigned long int dwFieldCount;     /* Or 0 if not determined until now ... */
    struct csvRecord* lpHeaderRecord;   /* If header reading is enabled the header record gets cached here */

    char sepChar;                       /* Separator char (by default it should be ",") */

    struct {
        csvParser_Callback_HeadersRead  callbackHeader;     void* lpFreeParam_Header;
        csvParser_Callback_RecordRead   callbackRecord;     void* lpFreeParam_Record;
        csvParser_Callback_Error        callbackError;      void* lpFreeParam_Error;
    } callbacks;

    struct csvRecord* lpCurrentRecords;
    unsigned long int dwCurrentFieldIndex;

    unsigned long int dwLineNumber;     /* Line number counter (used for error messages) */

    struct csvSystemAPI* lpSystem;      /* Reference to memory allocation and release */

    struct {
        struct stringCollectorElement* lpHead;
        struct stringCollectorElement* lpLast;
    } collector;
};
/*@
    predicate ccsvParser_ValidStructure(struct csvParser* p) =
        \valid(p)
        && \valid(&(p->parserState))
        && \valid(&(p->detectedLineSepChar))
            && ((p->detectedLineSepChar == 0x0A) || (p->detectedLineSepChar == 0x0D) || (p->detectedLineSepChar == 0x00))
        && \valid(&(p->dwFlags))
            && ((p->dwFlags & (~(CSVPARSER_FLAGS__QUIRKS_ALLOW_CR_LF_TERMINATION|CSVPARSER_FLAGS__QUIRKS_ALLOW_NONASCII|CSVPARSER_FLAGS__HEADERLINE_ENABLE))) == 0)
        && \valid(&(p->dwFieldCount))
            && (p->dwFieldCount >= 0)
        && \valid(&(p->lpHeaderRecord))
        && \valid(&(p->sepChar))
        && \valid(&(p->callbacks.callbackHeader)) && \valid(&(p->callbacks.lpFreeParam_Header))
        && \valid(&(p->callbacks.callbackRecord)) && \valid(&(p->callbacks.lpFreeParam_Record))
        && \valid(&(p->callbacks.callbackError)) && \valid(&(p->callbacks.lpFreeParam_Error))

        && \valid(&(p->lpCurrentRecords))
            && ((p->lpCurrentRecords == \null) || validCCSVCsvRecord(p->lpCurrentRecords))
        && \valid(&(p->dwCurrentFieldIndex))
            && (p->dwCurrentFieldIndex >= 0)

        && \valid(&(p->dwLineNumber))
            && (p->dwLineNumber >= 0)
        && validCCSVCsvSystem(p->lpSystem)

        && \valid(&(p->collector.lpHead))
        && \valid(&(p->collector.lpLast))
        && ((p->collector.lpHead == \null) || (\valid(p->collector.lpHead) && (p->collector.lpHead != \null)))
        && ((p->collector.lpLast == \null) || (\valid(p->collector.lpLast) && (p->collector.lpLast != \null)));
*/

#define csvParserCreate__ALLOWEDFLAGS (CSVPARSER_FLAGS__QUIRKS_ALLOW_CR_LF_TERMINATION|CSVPARSER_FLAGS__QUIRKS_ALLOW_NONASCII|CSVPARSER_FLAGS__HEADERLINE_ENABLE)
/*@
    requires (lpParserOut == \null)
            || ((lpParserOut != \null) && \valid(lpParserOut));
    requires ((dwFlags & ~csvParserCreate__ALLOWEDFLAGS) == 0);

    requires (callbackHeader == \null) || \valid_function(callbackHeader);
    requires (callbackRecord == \null) || \valid_function(callbackRecord);
    requires (callbackError == \null) || \valid_function(callbackError);

    requires validCCSVCsvSystem(lpSystem);

    behavior errNoParserOut:
        assumes (lpParserOut == \null);

        assigns \nothing;

        ensures \result == csvE_InvalidParam;

    behavior errInvalidFlags:
        assumes (lpParserOut != \null);
        assumes ((dwFlags & ~csvParserCreate__ALLOWEDFLAGS) != 0);

        assigns (*lpParserOut);

        ensures (*lpParserOut) == \null;
        ensures \result == csvE_InvalidParam;

    behavior correctParameter:
        assumes (lpParserOut != \null);
        assumes ((dwFlags & ~csvParserCreate__ALLOWEDFLAGS) == 0);

        ensures (((*lpParserOut) == \null) && (\result == csvE_OutOfMemory))
                || (((*lpParserOut) != \null)
                    && (\result == csvE_Ok)
                    && ccsvParser_ValidStructure(*lpParserOut)
                    && ((*lpParserOut)->parserState == csvParserState_IDLE)
                    && ((*lpParserOut)->detectedLineSepChar == 0x00)
                    && ((*lpParserOut)->dwFlags == dwFlags)
                    && ((*lpParserOut)->dwFieldCount == 0)
                    && (((*lpParserOut)->lpHeaderRecord == \null) || \valid((*lpParserOut)->lpHeaderRecord))
                    && (((*lpParserOut)->lpCurrentRecords == \null) || \valid((*lpParserOut)->lpCurrentRecords))
                    && ((((*lpParserOut)->lpHeaderRecord == \null) && ((*lpParserOut)->lpCurrentRecords != \null)) || (((*lpParserOut)->lpHeaderRecord != \null) && ((*lpParserOut)->lpCurrentRecords == \null)))
                    && ((*lpParserOut)->sepChar == ',')
                    && ((*lpParserOut)->callbacks.callbackHeader == callbackHeader) && ((*lpParserOut)->callbacks.lpFreeParam_Header == lpFreeParam_Header)
                    && ((*lpParserOut)->callbacks.callbackRecord == callbackRecord) && ((*lpParserOut)->callbacks.lpFreeParam_Record == lpFreeParam_Record)
                    && ((*lpParserOut)->callbacks.callbackError == callbackError) && ((*lpParserOut)->callbacks.lpFreeParam_Error == lpFreeParam_Error)
                    && ((*lpParserOut)->dwCurrentFieldIndex == 0)
                    && ((*lpParserOut)->dwLineNumber == 0)
                    && ((*lpParserOut)->lpSystem == lpSystem)
                    && validCCSVCsvSystem((*lpParserOut)->lpSystem)
                );

    complete behaviors;
    disjoint behaviors;
*/
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
);
/*@
    requires (lpParser == \null) || ccsvParser_ValidStructure(lpParser);

    assigns \nothing;

    ensures (\result == csvE_Ok) || (\result == csvE_InvalidParam);
*/
enum csvError csvParserRelease(
    struct csvParser* lpParser
);
/*@
    requires (lpParser == \null) || ccsvParser_ValidStructure(lpParser);

    ensures (\result == csvE_Ok)
		|| (\result == csvE_InvalidParam)
		|| (\result == csvE_ParserError)
		|| (\result == csvE_OutOfMemory)
		|| (\result == csvE_Abort);
*/
enum csvError csvParserFinish(
    struct csvParser* lpParser
);
/*@
    requires (lpParser == \null) || ccsvParser_ValidStructure(lpParser);

    ensures (\result == csvE_Ok)
		|| (\result == csvE_InvalidParam)
		|| (\result == csvE_ParserError)
		|| (\result == csvE_OutOfMemory)
		|| (\result == csvE_Abort);
*/
enum csvError csvParserProcessByte(
    struct csvParser* lpParser,
    char bByte
);

/*
	Helper API for access using libc functions
*/
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
);

/*
    Serializer API
*/

struct csvWriter;

enum csvError csvWriterCreate(
    struct csvWriter** lpWriterOut,
    uint32_t dwFlags,

    struct csvSystemAPI* lpSystem
);
enum csvError csvWriterRelease(
    struct csvWriter* lpWriter
);
/* enum csvError csvWriterAppendRecord(
    struct csvWriter* lpWriter
); */

#ifdef __cplusplus
    } /* extern "C" { */
#endif

#endif /* #ifndef __is_included__e2db3911_45df_11ea_8fdc_b499badf00a1 */
