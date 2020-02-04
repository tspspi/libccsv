#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../include/ccsv.h"

static const char* lpTest1 = "Test1";
static const char* lpTest2 = "Test2";
static const char* lpTest3 = "Test3";
static const char* lpTest4 = "Test4";
static const char* lpReplaceTest = "Replacement Test";

int main(int argc, char* argv[]) {
    enum csvError e;

    /*
        Try to create and release

        First using malloc backend, then using a passed
        structure (also wrapping malloc)
    */
    {
        struct csvRecord* r;
        printf("\t%s:%u Creating record (malloc backend) ... ", __FILE__, __LINE__);
        e = csvRecordCreate(&r, 0, NULL);
        if(e != csvE_Ok) {
            printf("failed (%u)\n", e);
            return 1;
        }
        printf("ok\n");

        printf("\t%s:%u Releasing record ... ", __FILE__, __LINE__);
        e = csvRecordRelease(r);
        if(e != csvE_Ok) {
            printf("failed (%u)\n", e);
            return 1;
        }
        printf("ok\n");

        printf("\t%s:%u Calling release with NULL pointer ... ", __FILE__, __LINE__);
        e = csvRecordRelease(NULL);
        if(e != csvE_Ok) {
            printf("failed (%u)\n", e);
            return 1;
        }
        printf("ok\n");
    }

    /*
        Trying to accumulate some records, retreive them later on
        (using auto expanding)
    */
    {
        struct csvRecord* r;
        printf("\t%s:%u Creating record (malloc backend) ... ", __FILE__, __LINE__);
        e = csvRecordCreate(&r, 4, NULL);
        if(e != csvE_Ok) {
            printf("failed (%u)\n", e);
            return 1;
        }
        printf("ok\n");

        printf("\t%s:%u Field count %lu, Capacity %lu\n", __FILE__, __LINE__, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));

        printf("\t%s:%u Adding test 1 ... ", __FILE__, __LINE__); e = csvRecordSetField(r, 0, lpTest1, strlen(lpTest1)+1); if(e != csvE_Ok) { printf("failed (%u)\n", e); return 1; } else { printf("ok\n"); }
        printf("\t%s:%u Field count %lu, Capacity %lu\n", __FILE__, __LINE__, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        printf("\t%s:%u Adding test 2 ... ", __FILE__, __LINE__); e = csvRecordSetField(r, 1, lpTest2, strlen(lpTest2)+1); if(e != csvE_Ok) { printf("failed (%u)\n", e); return 1; } else { printf("ok\n"); }
        printf("\t%s:%u Field count %lu, Capacity %lu\n", __FILE__, __LINE__, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        printf("\t%s:%u Adding test 3 ... ", __FILE__, __LINE__); e = csvRecordSetField(r, 2, lpTest3, strlen(lpTest3)+1); if(e != csvE_Ok) { printf("failed (%u)\n", e); return 1; } else { printf("ok\n"); }
        printf("\t%s:%u Field count %lu, Capacity %lu\n", __FILE__, __LINE__, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        printf("\t%s:%u Adding test 4 ... ", __FILE__, __LINE__); e = csvRecordSetField(r, 3, lpTest4, strlen(lpTest4)+1); if(e != csvE_Ok) { printf("failed (%u)\n", e); return 1; } else { printf("ok\n"); }
        printf("\t%s:%u Field count %lu, Capacity %lu\n", __FILE__, __LINE__, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));

        const char* lpReceivedData;
        unsigned long int dwReceivedLen;
        unsigned long int i;

        for(i = 0; i < 4; i=i+1) {
            printf("\t%s:%u Reading field %lu ... ", __FILE__, __LINE__, i);
            e = csvRecordGetField(r, i, &lpReceivedData, &dwReceivedLen);
            if(e != csvE_Ok) {
                printf("failed (%u)\n", e);
                return 1;
            } else {
                printf("ok (%lu bytes): %.*s\n", dwReceivedLen, (int)(dwReceivedLen-1), lpReceivedData);
            }
        }

        printf("\t%s:%u Replacing first field ... ", __FILE__, __LINE__); e = csvRecordSetField(r, 0, lpReplaceTest, strlen(lpReplaceTest)+1); if(e != csvE_Ok) { printf("failed (%u)\n", e); return 1; } else { printf("ok\n"); }
        printf("\t%s:%u Field count %lu, Capacity %lu\n", __FILE__, __LINE__, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        for(i = 0; i < 4; i=i+1) {
            printf("\t%s:%u Reading field %lu ... ", __FILE__, __LINE__, i);
            e = csvRecordGetField(r, i, &lpReceivedData, &dwReceivedLen);
            if(e != csvE_Ok) {
                printf("failed (%u)\n", e);
                return 1;
            } else {
                printf("ok (%lu bytes): %.*s\n", dwReceivedLen, (int)(dwReceivedLen-1), lpReceivedData);
            }
        }

        printf("\t%s:%u Resizing. Old pointer %p ... ", __FILE__, __LINE__, (void*)r);
        e = csvRecordResize(&r, 8); if(e != csvE_Ok) { printf("failed (%u)\n", e); return 1; }
        printf("ok. New pointer %p\n", (void*)r);
        printf("\t%s:%u Field count %lu, Capacity %lu\n", __FILE__, __LINE__, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        printf("\t%s:%u Adding test 5 (string 2) ... ", __FILE__, __LINE__); e = csvRecordSetField(r, 4, lpTest2, strlen(lpTest2)+1); if(e != csvE_Ok) { printf("failed (%u)\n", e); return 1; } else { printf("ok\n"); }
        printf("\t%s:%u Field count %lu, Capacity %lu\n", __FILE__, __LINE__, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        for(i = 0; i < 5; i=i+1) {
            printf("\t%s:%u Reading field %lu ... ", __FILE__, __LINE__, i);
            e = csvRecordGetField(r, i, &lpReceivedData, &dwReceivedLen);
            if(e != csvE_Ok) {
                printf("failed (%u)\n", e);
                return 1;
            } else {
                printf("ok (%lu bytes): %.*s\n", dwReceivedLen, (int)(dwReceivedLen-1), (lpReceivedData == NULL) ? "NULL" : lpReceivedData);
            }
        }

        printf("\t%s:%u Releasing record ... ", __FILE__, __LINE__);
        e = csvRecordRelease(r);
        if(e != csvE_Ok) {
            printf("failed (%u)\n", e);
            return 1;
        }
        printf("ok\n");
    }

    {
        struct csvRecord* r;
        enum csvError e;
        printf("\t%s:%u Creating record (malloc backend) ... ", __FILE__, __LINE__);
        e = csvRecordCreate(&r, 0, NULL);
        if(e != csvE_Ok) {
            printf("failed (%u)\n", e);
            return 1;
        }
        printf("ok\n");


        printf("\t%s:%u Resizing. Old pointer %p (fields %lu, used %lu) ... ", __FILE__, __LINE__, (void*)r, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        e = csvRecordAppendField(&r, 0, lpTest1, strlen(lpTest1)+1, NULL);
        if(e != csvE_Ok) { printf("failed (%u)\n", e); } else { printf("ok\n"); }
        printf("\t%s:%u Resizing. Old pointer %p (fields %lu, used %lu) ... ", __FILE__, __LINE__, (void*)r, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        e = csvRecordAppendField(&r, 1, lpTest2, strlen(lpTest2)+1, NULL);
        if(e != csvE_Ok) { printf("failed (%u)\n", e); } else { printf("ok\n"); }
        printf("\t%s:%u Resizing. Old pointer %p (fields %lu, used %lu) ... ", __FILE__, __LINE__, (void*)r, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        e = csvRecordAppendField(&r, 2, lpTest3, strlen(lpTest3)+1, NULL);
        if(e != csvE_Ok) { printf("failed (%u)\n", e); } else { printf("ok\n"); }
        printf("\t%s:%u Resizing. Old pointer %p (fields %lu, used %lu) ... ", __FILE__, __LINE__, (void*)r, csvRecordGetFieldCount(r), csvRecordGetFieldCountCapacity(r));
        e = csvRecordAppendField(&r, 3, lpTest4, strlen(lpTest4)+1, NULL);
        if(e != csvE_Ok) { printf("failed (%u)\n", e); } else { printf("ok\n"); }


        const char* lpReceivedData;
        unsigned long int dwReceivedLen;
        unsigned long int i;
        for(i = 0; i < 4; i=i+1) {
            printf("\t%s:%u Reading field %lu ... ", __FILE__, __LINE__, i);
            e = csvRecordGetField(r, i, &lpReceivedData, &dwReceivedLen);
            if(e != csvE_Ok) {
                printf("failed (%u)\n", e);
                return 1;
            } else {
                printf("ok (%lu bytes): %.*s\n", dwReceivedLen, (int)(dwReceivedLen-1), lpReceivedData);
            }
        }


        printf("\t%s:%u Releasing record ... ", __FILE__, __LINE__);
        e = csvRecordRelease(r);
        if(e != csvE_Ok) {
            printf("failed (%u)\n", e);
            return 1;
        }
        printf("ok\n");
    }

    return 0;
}
