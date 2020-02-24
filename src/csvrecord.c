#include "../include/ccsv.h"
#include <stdlib.h>
#include <string.h>

#ifdef __cplusplus
    extern "C" {
#endif

enum csvError csvRecordCreate(
    struct csvRecord** lpOut,
    unsigned long int dwInitialFieldCount,

    struct csvSystemAPI* lpSystem
) {
    unsigned long int i;
    enum csvError e;

    if(lpOut == NULL) { return csvE_InvalidParam; }
    (*lpOut) = NULL;

    if(lpSystem == NULL) {
        (*lpOut) = (struct csvRecord*)malloc(sizeof(struct csvRecord) + dwInitialFieldCount*sizeof(((struct csvRecord*)0)->fields[0]));
        if((*lpOut) == NULL) {
            return csvE_OutOfMemory;
        }
    } else {
        if((lpSystem->alloc == NULL) || (lpSystem->free == NULL)) { return csvE_InvalidParam; }
        e = lpSystem->alloc(lpSystem, sizeof(struct csvRecord) + dwInitialFieldCount*sizeof(((struct csvRecord*)0)->fields[0]), (void**)lpOut);
        if(e != csvE_Ok) {
            return e;
        }
    }

    (*lpOut)->dwFieldCount = dwInitialFieldCount;
    (*lpOut)->dwUsedFieldCount = 0;
    (*lpOut)->lpSystem = lpSystem;

    for(i = 0; i < dwInitialFieldCount; i=i+1) {
        (*lpOut)->fields[i].dwDataLen = 0;
        (*lpOut)->fields[i].lpData = NULL;
    }

    return csvE_Ok;
}
enum csvError csvRecordRelease(
    struct csvRecord* lpRecord
) {
    unsigned long int i;
    if(lpRecord == NULL) { return csvE_Ok; }
    struct csvSystemAPI* lpSystem;

    lpSystem = lpRecord->lpSystem;

    if(lpSystem == NULL) {
        for(i = 0; i < lpRecord->dwFieldCount; i=i+1) {
            if(lpRecord->fields[i].lpData != NULL) {
                free((void*)(lpRecord->fields[i].lpData));
                lpRecord->fields[i].lpData = NULL;
                lpRecord->fields[i].dwDataLen = 0;
            }
        }
        free((void*)lpRecord);
    } else {
        for(i = 0; i < lpRecord->dwFieldCount; i=i+1) {
            if(lpRecord->fields[i].lpData != NULL) {
                lpSystem->free(lpSystem, (void*)(lpRecord->fields[i].lpData));
                lpRecord->fields[i].lpData = NULL;
                lpRecord->fields[i].dwDataLen = 0;
            }
        }
        lpSystem->free(lpSystem, (void*)lpRecord);
    }
    return csvE_Ok;
}
enum csvError csvRecordResize(
    struct csvRecord** lpRecordInOut,
    unsigned long int dwNewFieldCount
) {
    enum csvError e;
    struct csvRecord* lpNewRecord;
    unsigned long int i;

    if(lpRecordInOut == NULL) { return csvE_InvalidParam; }
    if(dwNewFieldCount < (*lpRecordInOut)->dwUsedFieldCount) { return csvE_InvalidParam; }

    e = csvRecordCreate(&lpNewRecord, dwNewFieldCount, (*lpRecordInOut)->lpSystem);
    if(e != csvE_Ok) { return e; }

    lpNewRecord->dwUsedFieldCount = (*lpRecordInOut)->dwUsedFieldCount;
    lpNewRecord->dwFieldCount = dwNewFieldCount;
    for(i = 0; i < lpNewRecord->dwUsedFieldCount; i=i+1) {
        lpNewRecord->fields[i].lpData = (*lpRecordInOut)->fields[i].lpData;
        lpNewRecord->fields[i].dwDataLen = (*lpRecordInOut)->fields[i].dwDataLen;
        (*lpRecordInOut)->fields[i].lpData = NULL;
        (*lpRecordInOut)->fields[i].dwDataLen = 0;
    }

    csvRecordRelease((*lpRecordInOut));
    (*lpRecordInOut) = lpNewRecord;
    return csvE_Ok;
}
/*@
    requires (\valid(lpRecordIn) && \valid_read(&lpRecordIn->dwUsedFieldCount)) || (lpRecordIn == \null);

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
) {
    if(lpRecordIn == NULL) { return 0; }
    return lpRecordIn->dwUsedFieldCount;
}
/*@
    requires (\valid(lpRecordIn) && \valid_read(&lpRecordIn->dwFieldCount)) || (lpRecordIn == \null);

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
) {
    if(lpRecordIn == NULL) { return 0; }
    return lpRecordIn->dwFieldCount;
}
enum csvError csvRecordGetField(
    struct csvRecord* lpRecord,
    unsigned long int dwFieldIndex,

    const char** lpData_Out,
    unsigned long int* lpDataLen_Out
) {
    if(lpData_Out != NULL) { (*lpData_Out) = NULL; }
    if(lpDataLen_Out == 0) { (*lpDataLen_Out) = 0; }

    if(lpRecord == NULL) { return csvE_InvalidParam; }

    if(dwFieldIndex >= lpRecord->dwUsedFieldCount) { return csvE_IndexOutOfBounds; }

    (*lpData_Out) = lpRecord->fields[dwFieldIndex].lpData;
    (*lpDataLen_Out) = lpRecord->fields[dwFieldIndex].dwDataLen;
    return csvE_Ok;
}
enum csvError csvRecordSetField(
    struct csvRecord* lpRecord,
    unsigned long int dwFieldIndex,

    const char* lpDataIn,
    unsigned long int dwDataLen
) {
    enum csvError e;
    char* lpNewBuffer;

    if(lpRecord == NULL) { return csvE_InvalidParam; }

    if(dwFieldIndex >= lpRecord->dwFieldCount) {
        return csvE_IndexOutOfBounds;
    }

    if(lpRecord->fields[dwFieldIndex].lpData != NULL) {
        if(lpRecord->lpSystem == NULL) {
            free((void*)(lpRecord->fields[dwFieldIndex].lpData));
        } else {
            lpRecord->lpSystem->free(lpRecord->lpSystem, (void*)(lpRecord->fields[dwFieldIndex].lpData));
        }
        lpRecord->fields[dwFieldIndex].lpData = NULL;
        lpRecord->fields[dwFieldIndex].dwDataLen = 0;
    }

    if(lpRecord->lpSystem == NULL) {
        lpNewBuffer = (char*)malloc(dwDataLen);
        if(lpNewBuffer == NULL) {
            return csvE_OutOfMemory;
        }
    } else {
        e = lpRecord->lpSystem->alloc(lpRecord->lpSystem, dwDataLen, (void**)(&lpNewBuffer));
        if(e != csvE_Ok) {
            return e;
        }
    }
    memcpy(lpNewBuffer, lpDataIn, dwDataLen);
    lpRecord->fields[dwFieldIndex].lpData = lpNewBuffer;
    lpRecord->fields[dwFieldIndex].dwDataLen = dwDataLen;
    if(dwFieldIndex >= lpRecord->dwUsedFieldCount) {
        lpRecord->dwUsedFieldCount = dwFieldIndex+1;
    }
    return csvE_Ok;
}
enum csvError csvRecordAppendField(
    struct csvRecord** lpRecord,
    unsigned long int dwFieldIndex,

    const char* lpDataIn,
    unsigned long int dwDataLen,

    struct csvSystemAPI* lpSystem
) {
    enum csvError e;

    if(lpRecord == NULL) { return csvE_InvalidParam; }
    if((*lpRecord) == NULL) {
        e = csvRecordCreate(lpRecord, 1, lpSystem);
        if(e != csvE_Ok) { return e; }
    } else if(dwFieldIndex >= (*lpRecord)->dwFieldCount) {
        e = csvRecordResize(lpRecord, dwFieldIndex+1);
        if(e != csvE_Ok) { return e; }
    }

    return csvRecordSetField((*lpRecord), dwFieldIndex, lpDataIn, dwDataLen);
}

#ifdef __cplusplus
    } /* extern "C" { */
#endif