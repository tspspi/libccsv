# CSV parser library (libccsv)

Note: _The ACSL contracts as well as the proof for the parser to be RTE-free
is work in progress_.

This is a small and simple ANSI C parser library for ```comma-separated values``` (CSV)
files as specified in [RFC 4180](https://tools.ietf.org/html/rfc4180).
It handles:

* Input data validation
* Header line handling
* Handling of value quoting
* Record handling
* Provides helper routines to simply pass a filename and process the content
* Provides a wrapper around single records

## Usage examples

Till documentation is finished the following test programs are useful
examples for library usage:

* ```tests/001_csvrecord.c``` can be used as a summary for ```csvRecord```
  handling functions.
* ```tests/002_csvread.c``` shows how one can use the push parser to handle
  streams of CSV data.
* ```tests/003_parserhelper01``` shows how to easily read an CSV file by
  supplying the filename and callback functions.

The following section describes the basic concepts and basic usage.

### Reading CSV from a file

To simply read from a file in ANSI C using the libc's file input/output
routines there exists a helper function ```csvParserHelper_ProcessFile```
that can be used. This function wraps creation and configuration
of the parser as well as opening, reading and closing the file.

The function uses (as all parser functions) callbacks. There are three
optional callbacks available. Any callback that is not specifies (i.e. was
passed ```NULL```) will not be invoked:

* A header line callback that's called once for a header line if
  headerline processing has been enabled (```CSVPARSER_FLAGS__HEADERLINE_ENABLE```)
  flag passed to the parser function. If headerline processing has not
  been enabled this callback won't be called.
* A record callback that's called once for each line in the CSV. It returns
  an ```struct csvRecord``` object that one can access using the appropriate
  functions.
* An error callback that's called on parsing errors or other error conditions.

Each callback is capable of getting passed a transparent ```void*``` to keep
state or any other kind of external information.

#### Header and record callbacks

The header and record callbacks have the same signature:

```
static enum csvError callback(
	struct csvParser* lpP,
	void* lpFreeParam,
	struct csvRecord* lpHeaderLine
);
```

They return ```csvE_Ok``` whenever the supplied callback accepts the
passed record. In case of the header line the callback is _not_ allowed
to release the record, in case of data callbacks the callback is _required_
to release the record in case ```csvE_Ok``` has been returned. In any
other case the library will handle releasing the record object transparently.

#### Error callback

The error callback as a different signature:

```
static enum csvError callback(
	struct csvParser* lpP,
	void* lpFreeParam,
	enum csvError eCode,
	unsigned long int dwLineNumber
);
```
Since resumption of parsing is currently not implemented the return value
should always be ```csvE_Ok```

#### Flags that can be passed

* ```CSVPARSER_FLAGS__HEADERLINE_ENABLE``` enables headerline processing. In
  this case the first line is threatened as a line that contains column
  headers. This allows code  to parse files having different fields or field
  order.
* ```CSVPARSER_FLAGS__QUIRKS_ALLOW_NONASCII``` disables input validation for
 allowed characters. By specification CSV files are only allowed to contain
 US ASCII symbols (see [RFC 4180](https://tools.ietf.org/html/rfc4180)). If
 this flag is set the parser supports reading UTF-8 files for example.
* ```CSVPARSER_FLAGS__QUIRKS_ALLOW_CR_LF_TERMINATION``` disables input
 validation. By specification CSV files always have to have their lines
 terminated by a carriage return (CR) followed by a linefeed (LF). This is
 sometimes violated by CSV files that are created on Unix-like/Linux systems
 since their native termination often only consists of CR or LF. If this
 flag is set an arbitrary termination is accepted. The parser simply
 remembers the first or the line termination symbols and ignores any other
 seen character code.

#### Providing own allocation/deallocation functions

It's possible to use the parser with custom allocation/deallocation functions.
This is useful in some situations when using custom pooling allocators or
object caches. To support custom allocators one can pass an
structure ```struct csvSystemAPI``` to the instantiation function of parsers
and/or records. This structure contains a pointer to a custom ```alloc```
and ```free``` function. These have a somewhat unusual signature:

```
struct csvSystemAPI {
    csvSystemAPI_Alloc                          alloc;
    csvSystemAPI_Free                           free;
};

typedef enum csvError (*csvSystemAPI_Alloc)(
	struct csvSystemAPI*						lpSelf,
	unsigned long int							dwSize,
	void**										lpDataOut
);
typedef enum csvError (*csvSystemAPI_Free)(
	struct csvSystemAPI*						lpSelf,
	void*										lpObject
);
```

The ```csvSystemAPI``` structure is passed to allow passing of state information
of information equivalent to an ```this``` pointer into the allocation and
free function. The memory offset is returned into the ```lpDataOut```
destination if successful. The functions should return ```csvE_Ok``` in case
of success or are expected to return ```csvE_OutOfMemory``` or ```csvE_InvalidParam```
in case of memory exhaustion or invalid parameters.

Note that most of the time this feature will not be required so one should
simply pass ```NULL```.

Currently verification also assumes standard libc malloc/free to be used. This
is currently enforced by ghost code (that's usually considered unacceptable
for formal verification).

#### Parsing

Using all that mentioned information from above parsing a single CSV file
is rather simple:

```
/*
	Declare the required callbacks
*/

static enum csvError csvCallback_HeaderLine(
	struct csvParser* lpP,
	void* lpFreeParam,
	struct csvRecord* lpHeaderLine
) {
	return csvE_Ok;
}

static enum csvError csvCallback_RecordLine(
	struct csvParser* lpP,
	void* lpFreeParam,
	struct csvRecord* lpRecord
) {
	csvRecordRelease(lpData);
	return csvE_Ok;
}

static enum csvError csvCallback_HeaderLine(
	struct csvParser* lpP,
	void* lpFreeParam,
	enum csvError eCode,
	unsigned long int dwLineNumber
) {
	return csvE_Ok;
}

/*
	And just invoke the parser where required ...
*/

int main(int argc, char* argv[]) {
	// ...

	enum csvError e;
	e = csvParserHelper_ProcessFile(
        argv[1],
        CSVPARSER_FLAGS__HEADERLINE_ENABLE,
		&csvCallback_HeaderLine, NULL,
		&csvCallback_DataLine, NULL,
		&csvCallback_Error, NULL,
		NULL
    );

	// ...
}
```

#### Accessing fields

The record can be accessed using csvRecord functions. These are:

* ```csvRecordGetField(struct csvRecord* lpRecord, unsigned long int dwFieldIndex, const char** lpData_Out, unsigned long int* lpDataLen_Out)```
  simply returns the field data. The locations ```lpDataOut``` and ```lpDataLen_Out```
  variables are set to the appropriate pointers and length. Note that data used
  by this library is normally __not zero terminated__.
* ```csvRecordSetField(struct csvRecord* lpRecord, unsigned long int dwFieldIndex, const char* lpDataIn, unsigned long int dwDataLen)```
  is normally only used during serialization. It sets the appropriate field
  data. Note that this function does not take ownership of the data
  but performs a fully copy of all data.

In addition there is a number of other functions associated with records:

* ```csvRecordCreate``` to instantiate a new record. This is normally only
  required  for the serializer, not for the reader.
* ```csvRecordRelease``` allows one to release all resources associated with
  a given record (i.e. all fields)
* ```csvRecordResize``` is mostly used internally to resize the capacity of
  an record (i.e. add additional columns)
* ```csvRecordGetFieldCount``` determines the number of columns used inside
  the record.
* ```csvRecordGetFieldCountCapacity``` is normally used internally and determines
  the available capacity inside the record (a record can be larger than required)
* ```csvRecordAppendField``` simply pushes additional data into the record structure.
  This function is used during parsing and extends the record if the capacity is not
  sufficient.
