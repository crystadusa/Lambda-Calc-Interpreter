#pragma once

#include <stdio.h>
#include <stdlib.h>

// Binds overflow detection for each compiler
#ifdef __GNUC__
#define OVERFLOW_ADD_I32(lhs, rhs) __builtin_add_overflow(lhs, rhs, &lhs)
#define OVERFLOW_MUL_I32(lhs, rhs) __builtin_mul_overflow(lhs, rhs, &lhs)
#elif _MSC_VER
#include <intrin.h>
#define OVERFLOW_ADD_I32(lhs, rhs) _add_overflow_i32(0, lhs, rhs, &lhs)
#define OVERFLOW_MUL_I32(lhs, rhs) _mul_overflow_i32(lhs, rhs, &lhs)
#else
#error Overflow detection is not implemented for this compiler
#endif

// Includes and binds the tracy profiler for instrumentation
#ifdef TRACY_ENABLE
#include <tracy/public/tracy/TracyC.h>
#define PROFILE_SCOPE() TracyCZone(__profile, 1)
#define PROFILE_NAMED(name) TracyCZoneN(__profile, name, 1)
#define PROFILE_CONTEXT(name, context) TracyCZoneN(context, name, 1)
#define PROFILE_END() TracyCZoneEnd(__profile)
#define PROFILE_END_CONTEXT(context) TracyCZoneEnd(context)
#else
#define PROFILE_SCOPE()
#define PROFILE_NAMED(name)
#define PROFILE_CONTEXT(name, context)
#define PROFILE_END()
#define PROFILE_END_CONTEXT(context)
#endif

// implementation of dynamically sized arrays
typedef struct {
    void* Data;
    int Size;
    int Capacity;
} Array;

#define Array(Type) typedef struct {\
    Type* Data;\
    int Size;\
    int Capacity;\
} Type##Array

// Constants to initialize buffers and limit recursion
#define MAX_INT_CHARS 10
#define START_BUFFER_SIZE 4096
#define TEST_RECURSION_COUNT 4096

// Data layout of types for lambda evaluation
typedef struct {
	int Size;
	int InputID; // BoundId when Size is 1 and AbstractionCount otherwise
} Func;

typedef struct {
    int Index;
    int InputCount;
    int ArgumentIndex;
	int LastIndex;
	int PrevIndex;
} FuncStack;

typedef struct {
    int IsReduced;
    int Index;
} FuncArg;

typedef struct {
    int ScopeOffset;
    int OffsetEnd;
} Abstraction;

Array(Func);
Array(FuncStack);
Array(FuncArg);
Array(Abstraction);

// Function prototypes
int ResizeArray(void*, int);
void UpdateFuncSize(Func*, FuncStack*, int, FuncArg*, int, int, int);
int CallFunc(Func*, int, FuncArray*, int);
int IntToChars(char*, int);
