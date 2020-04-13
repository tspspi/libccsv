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
