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



    csvE_ImplementationError                = 255
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

enum csvError csvRecordCreate(
    struct csvRecord** lpOut,
    unsigned long int dwInitialFieldCount,

    struct csvSystemAPI* lpSystem
);
enum csvError csvRecordRelease(
    struct csvRecord* lpRecord
);
enum csvError csvRecordResize(
    struct csvRecord** lpRecordInOut,
    unsigned long int dwNewFieldCount
);
unsigned long int csvRecordGetFieldCount(
    struct csvRecord* lpRecordIn
);
unsigned long int csvRecordGetFieldCountCapacity(
    struct csvRecord* lpRecordIn
);

enum csvError csvRecordGetField(
    struct csvRecord* lpRecord,
    unsigned long int dwFieldIndex,

    const char** lpData_Out,
    unsigned long int* lpDataLen_Out
);
enum csvError csvRecordSetField(
    struct csvRecord* lpRecord,
    unsigned long int dwFieldIndex,

    const char* lpDataIn,
    unsigned long int dwDataLen
);
enum csvError csvRecordAppendField(
    struct csvRecord** lpRecord,
    unsigned long int dwFieldIndex,

    const char* lpDataIn,
    unsigned long int dwDataLen,

    struct csvSystemAPI* lpSystem
);

/*
    System API
*/

struct csvSystemAPI;
typedef enum csvError (*csvSystemAPI_Alloc)(
	struct csvSystemAPI*						lpSelf,
	unsigned long int							dwSize,
	void**										lpDataOut
);
typedef enum csvError (*csvSystemAPI_Free)(
	struct csvSystemAPI*						lpSelf,
	void*										lpObject
);

struct csvSystemAPI {
    csvSystemAPI_Alloc                          alloc;
    csvSystemAPI_Free                           free;
};

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
    void* lpFreeParam
    /* Record containing header lines ... */
);
typedef enum csvError (*csvParser_Callback_RecordRead)(
    struct csvParser* lpParser,
    void* lpFreeParam
    /* Record containing data ... */
);
typedef enum csvError (*csvParser_Callback_Error)(
    struct csvParser* lpParser,
    void* lpFreeParam,
    enum csvError eCode,
    unsigned long int dwLineNumber
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
);
enum csvError csvParserRelease(
    struct csvParser* lpParser
);
enum csvError csvParserProcessByte(
    struct csvParser* lpParser,
    char bByte
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
    struct {
        struct stringCollectorElement* lpHead;
        struct stringCollectorElement* lpLast;
    } collector;

    unsigned long int dwLineNumber;     /* Line number counter (used for error messages) */

    struct csvSystemAPI* lpSystem;      /* Reference to memory allocation and release */
};

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
