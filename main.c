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
#include <stdlib.h>

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

static int ResizeArray(void* DynArray, int Size) {
    Array* Data = (Array*) 1;
    Array* Array = DynArray;
    if (Array->Capacity < Size) {
        // Doubles capacity or until it can hold the new size
        PROFILE_SCOPE();
        Array->Capacity *= 2;
        if (Array->Capacity < Size) Array->Capacity = Size;

        // Reallocates memory into a larger buffer
        Data = realloc(Array->Data, Array->Capacity);
        if (Data) Array->Data = Data;
        PROFILE_END();
    }

    // Returns an error code if realloc fails
    return Data ? 0 : 1;
}

// Constants to initialize buffers and limit recursion
#define StartBufferSize 4096
#define MaxRecursionCount 4096

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

static void UpdateFuncSize(Func* Output, FuncStack* Funcs, int FuncIndex, FuncArg* FuncArgs, int MaxInputIndex, int FirstIndex, int SizeOffset) {
    PROFILE_SCOPE();

    // Updates sized terms
	for (int i = 0; i < FirstIndex; i++)
		if (Output[i].Size > FirstIndex - i)
			Output[i].Size += SizeOffset;

    // Updates function end positions
    for (int i = FuncIndex + 1; i;)
        if (Funcs[--i].LastIndex > FirstIndex)
            Funcs[i].LastIndex += SizeOffset;

    // Updates argument positions
    for (int i = 0; i < MaxInputIndex; i++)
        if (FuncArgs[i].Index > FirstIndex)
            FuncArgs[i].Index += SizeOffset;

    PROFILE_END();
}

static int CallFunc(Func* Called, int CalledCount, FuncArray* OutBuffer) {
    PROFILE_NAMED("Lambda evaluation");
    
    int ReturnValue = 1;
    int AbstractionsParsed = 0;
    int PostFreeVariable = 0;

    // Resizes the output buffer to fit the input buffer
    FuncArray Output = *OutBuffer;
    if (ResizeArray(&Output, CalledCount * sizeof (Func))) return 1;
    Output.Size = CalledCount;

    // Copies the input buffer to the output buffer
	for (int i = 0; i < CalledCount; i++)
    	Output.Data[i] = Called[i];

    // Allocates memory buffers and returns on failure
    // Aside from FuncArgs, the size field is treated as the last index
    AbstractionArray Abstractions = {0};
    FuncArgArray FuncArgs = {0};
	FuncStackArray Funcs = {0};
    FuncArray ReductionBuffer = {0};
    if (ResizeArray(&Abstractions, StartBufferSize) || ResizeArray(&FuncArgs, StartBufferSize) ||
        ResizeArray(&Funcs, StartBufferSize) || ResizeArray(&ReductionBuffer, StartBufferSize)) goto CallFuncDefer;
    
    // Initializes a sentinel for function lookups
    Funcs.Data[0] = (FuncStack) {
        .Index = 0,
        .InputCount = 0,
        .ArgumentIndex = 0,
        .LastIndex = Output.Size,
        .PrevIndex = 0,
    };
	
	for (int i = 0; i < Output.Size || Funcs.Size;) {
        // Removes arguments and groupings after parseing a function
    	if (i >= Funcs.Data[Funcs.Size].LastIndex) {
            PROFILE_NAMED("Removeing arguments");

            // Calculates the number of preceding groupings ending before or at the end of the current function
            int F = Funcs.Size;
            int GroupingCount = F;
            for (int Index = Funcs.Data[Funcs.Size].Index; --Index && Output.Data[Index].Size > 1 && Output.Data[Index].InputID + Funcs.Data[F - 1].InputCount == 0 && i >= Index + Output.Data[Index].Size; F--);
            GroupingCount -= F;

            // Calculates if the current function is now a grouping ending where the following sized term ends
            int FuncOffset = GroupingCount;
            int Index = Funcs.Data[Funcs.Size].Index;
            GroupingCount += Output.Data[Index].Size > 1 && Output.Data[Index].InputID == 0 && Output.Data[Index].Size == 1 + Output.Data[Index + 1].Size;

            int LastInputIndex = i;
            if (Funcs.Data[Funcs.Size].InputCount) {
                // Removes applied variables from earlier abstraction terms
                LastInputIndex = FuncArgs.Data[FuncArgs.Size - 1].Index;
                for (int j = Funcs.Size - 1; j && Funcs.Data[j].PrevIndex == 0 && (Funcs.Data[j].InputCount == 0 || FuncArgs.Data[Funcs.Data[j].ArgumentIndex].Index < LastInputIndex); j--)
                    Funcs.Data[j].InputCount = 0;

                // Updates size and positions from removing arguments
                LastInputIndex += Output.Data[LastInputIndex].Size;
                for (int j = i; j < LastInputIndex; j += Output.Data[j].Size)
                    UpdateFuncSize(Output.Data, Funcs.Data, Funcs.Size, FuncArgs.Data, Funcs.Data[Funcs.Size].ArgumentIndex, i, -Output.Data[j].Size);
            }

            // Updates size and positions from removing groupings
            if (GroupingCount) UpdateFuncSize(Output.Data, Funcs.Data, F, FuncArgs.Data, FuncArgs.Size, Funcs.Data[F].Index, -GroupingCount);

            // Removes groupings and arguments from the output buffer
            if (GroupingCount || i != LastInputIndex) {
                for (int j = Funcs.Data[F].Index; j < i - GroupingCount; j++)
                    Output.Data[j] = Output.Data[j + GroupingCount];

                i -= GroupingCount;
                for (int j = 0; j < Output.Size - LastInputIndex; j++)
                    Output.Data[i + j] = Output.Data[LastInputIndex + j];

                Output.Size += i - LastInputIndex;
            }
        
            // Restores the previous parseing state
            if (Funcs.Data[Funcs.Size].PrevIndex) {
                i = Funcs.Data[Funcs.Size].PrevIndex - 1;
                PostFreeVariable = 0;
            }

            Funcs.Size -= FuncOffset;
            Funcs.Size--;
            FuncArgs.Size = Funcs.Data[Funcs.Size].ArgumentIndex + Funcs.Data[Funcs.Size].InputCount;
            PROFILE_END();
    	}
    	
        // Parses variables
    	else if (Output.Data[i].Size < 2) {
            // Determines the number of applied and unapplied variables
            // Stops counting when detecting a sentinel value or the current variable is bound to an abstraction
            int F = Funcs.Size + 1;
            int AppliedOffset = 0;
            int ScopedOffset = 0;
            do {
                AppliedOffset += Funcs.Data[--F].InputCount;
                ScopedOffset += Output.Data[Funcs.Data[F].Index].InputID;
             } while (F && Funcs.Data[F].PrevIndex == 0 && (AppliedOffset + ScopedOffset <= Output.Data[i].InputID || Funcs.Data[F].InputCount + Output.Data[Funcs.Data[F].Index].InputID == 0));
            ScopedOffset += AppliedOffset;

            // Detects sentinel values for unapplied bound variables and free variables
            int BoundID = Output.Data[i].InputID - ScopedOffset + Output.Data[Funcs.Data[F].Index].InputID + Funcs.Data[F].InputCount;
            if (F == 0 || Funcs.Data[F].PrevIndex || BoundID >= Funcs.Data[F].InputCount) {
                // Unapplied bound variables cannot be reduced so the applied variable count decreases their bound ID instead
                // Free variables do not need separate parseing when not evaluating arguments
                if (Funcs.Data[F].PrevIndex == 0) {
                    Output.Data[i++].InputID -= AppliedOffset;
                    continue;
                }

                // Potential arguments do not need to be removed again
                if (PostFreeVariable) {
                    i++;
                    continue;
                }

                // Finds the last function that is not a grouping
                PROFILE_NAMED("Free variable evaluation");
                int LastF = Funcs.Size;
                while (LastF && Funcs.Data[LastF].PrevIndex == 0 && Funcs.Data[LastF].InputCount + Output.Data[Funcs.Data[LastF].Index].InputID == 0) LastF--;

                // Free variables may later become bound when evaluating arguments
                // So Input IDs must be updated to remove potential arguments from functions
                int StackIndex = 0;
                Abstractions.Data[0] = (Abstraction) {
                    .ScopeOffset = 0,
                    .OffsetEnd = i
                };

                int F2 = F;
                for (int j = Funcs.Data[F].Index; j < i; j++) {
                    // Decreases the function index or scope offset at the end of an abstraction
                    while (F2 && j >= Funcs.Data[F2].LastIndex) F2--;
                    while (j >= Abstractions.Data[StackIndex].OffsetEnd) StackIndex--;

                    // Tracks the most recent function to later sum their input counts
                    // Increases the scope offset when parseing an abstraction
                    if (F2 < LastF && Funcs.Data[F2 + 1].Index == j) F2++;
                    else if (Output.Data[j].Size > 1 && Output.Data[j].InputID) {
                        if (ResizeArray(&Abstractions, (++StackIndex + 1) * sizeof (Abstraction))) goto CallFuncDefer;
                        Abstractions.Data[StackIndex].ScopeOffset = Abstractions.Data[StackIndex - 1].ScopeOffset + Output.Data[j].InputID;
                        Abstractions.Data[StackIndex].OffsetEnd = j + Output.Data[j].Size;
                    }

                    if (Output.Data[j].Size == 1 && Output.Data[j].InputID >= Abstractions.Data[StackIndex].ScopeOffset) {
                        // Stops counting potential inputs when detecting a sentinel value or the current variable is bound to an abstraction
                        int F3 = F2 + 1;
                        int AppliedOffset = 0;
                        int ScopedOffset = Abstractions.Data[StackIndex].ScopeOffset;
                        do {
                            AppliedOffset += Funcs.Data[--F3].InputCount;
                            ScopedOffset += Output.Data[Funcs.Data[F3].Index].InputID;
                        } while (F3 && Funcs.Data[F3].PrevIndex == 0 && (ScopedOffset <= Output.Data[j].InputID || Funcs.Data[F3].InputCount + Output.Data[Funcs.Data[F3].Index].InputID == 0));

                        // Increases previous InputID with the new potential arguments
                        // if (F2 == LastF) AppliedOffset -= Funcs.Data[LastF].InputCount;
                        Output.Data[j].InputID += AppliedOffset;
                    }
                }

                // Removes inputs because they are now potential arguments of a free variable
                for (int j = F; j <= LastF; j++) {
                    Output.Data[Funcs.Data[j].Index].InputID += Funcs.Data[j].InputCount;
                    Funcs.Data[j].InputCount = 0;
                }

                PostFreeVariable = 1;
                // Output.Data[i++].InputID -= Funcs.Data[LastF].InputCount;
                i++;
                PROFILE_END();
                continue;
            }

            // The lazy reduction strategy parses arguments right before reduction
            int ArgumentIndex = FuncArgs.Data[Funcs.Data[F].ArgumentIndex + BoundID].Index;
            if (FuncArgs.Data[Funcs.Data[F].ArgumentIndex + BoundID].IsReduced == 0) {
                // The previous index is a sentinel that stores the reduction position
                if (ResizeArray(&Funcs, (++Funcs.Size + 1) * sizeof (FuncStack))) goto CallFuncDefer;
                Funcs.Data[Funcs.Size] = (FuncStack) {
                    .Index = ArgumentIndex,
                    .InputCount = 0,
                    .ArgumentIndex = FuncArgs.Size,
                    .LastIndex = ArgumentIndex + Output.Data[ArgumentIndex].Size,
                    .PrevIndex = i + 1,
                };

                // Marks the selected argument as reduced before parsing
                FuncArgs.Data[Funcs.Data[F].ArgumentIndex + BoundID].IsReduced = 1;
                i = ArgumentIndex;
                continue;
            }

            // Variables free to arguments need to skip argument applied to previous abstractions so the scoped argument count is updated
            PROFILE_NAMED("Bound variable evaluation");
            for (int j = F - 1; j && Funcs.Data[j].PrevIndex == 0 && (Funcs.Data[j].InputCount == 0 || FuncArgs.Data[Funcs.Data[j].ArgumentIndex].Index < ArgumentIndex); j--)
                ScopedOffset += Funcs.Data[j].InputCount;

            // Applies a beta reduction
            int BufferIndex = 0;
            int StackIndex = 0;
            Abstractions.Data[0] = (Abstraction) {
                .ScopeOffset = 0,
                .OffsetEnd = ArgumentIndex + Output.Data[ArgumentIndex].Size
            };

            // Resizes the output and reduction buffers to fit the reduced argument
            int SizeOffset = Output.Data[ArgumentIndex].Size - 1;
            if (ResizeArray(&Output, (Output.Size + SizeOffset) * sizeof (Func))) goto CallFuncDefer;
            if (ResizeArray(&ReductionBuffer, (SizeOffset + Output.Size - i) * sizeof (Func))) goto CallFuncDefer;

            for (int j = ArgumentIndex; j < ArgumentIndex + Output.Data[ArgumentIndex].Size; j++) {
                // Decreases the scope offset at the end of an abstraction
                while (j >= Abstractions.Data[StackIndex].OffsetEnd)
                    StackIndex--;

                // Use the scoped argument count to increase bound IDs for variables that are free or bounded outside the current abstraction
                ReductionBuffer.Data[BufferIndex++] = Output.Data[j];
                if (Output.Data[j].Size == 1 && Output.Data[j].InputID >= Abstractions.Data[StackIndex].ScopeOffset)
                    ReductionBuffer.Data[BufferIndex - 1].InputID += ScopedOffset;
                
                // Increases the scope offset when parseing an abstraction
                else if (Output.Data[j].InputID) {
                    if (ResizeArray(&Abstractions, (++StackIndex + 1) * sizeof (Abstraction))) goto CallFuncDefer;
                    Abstractions.Data[StackIndex].ScopeOffset = Abstractions.Data[StackIndex - 1].ScopeOffset + Output.Data[j].InputID;
                    Abstractions.Data[StackIndex].OffsetEnd = j + Output.Data[j].Size;
                }
            }

            // Moves a term to the reduction position for when the argument is only one term long
            Output.Data[i] = ReductionBuffer.Data[0];

            if (SizeOffset) {
                // Appends the output buffer at the reduction position to the reduction buffer
                for (int j = 0; j < Output.Size - i - 1; j++)
                    ReductionBuffer.Data[BufferIndex + j] = Output.Data[i + 1 + j];

                Output.Size += SizeOffset;

                // Moves the reduction buffer to the output buffer at the reduction position
                for (int j = i + 1; j < Output.Size; j++)
                    Output.Data[j] = ReductionBuffer.Data[j - i];
            
                UpdateFuncSize(Output.Data, Funcs.Data, Funcs.Size, FuncArgs.Data, FuncArgs.Size, i, SizeOffset);
            }
            PROFILE_END();
    	}

        // Parses groupings
        else if (Output.Data[i].InputID == 0) {
            if (i < Funcs.Data[Funcs.Size].LastIndex - 1 && Output.Data[i].Size - 1 == Output.Data[i + 1].Size) {
                PROFILE_NAMED("Grouping evaluation");

                // Removes groupings when they end where the following sized term ends
                Output.Size--;
                for (int j = i; j < Output.Size; j++)
                    Output.Data[j] = Output.Data[j + 1];

                UpdateFuncSize(Output.Data, Funcs.Data, Funcs.Size, FuncArgs.Data, FuncArgs.Size, i, -1);
                PROFILE_END();
            } else {
                // Handles groupings as a function
                if (ResizeArray(&Funcs, (++Funcs.Size + 1) * sizeof (FuncStack))) goto CallFuncDefer;
                Funcs.Data[Funcs.Size] = (FuncStack) {
                    .Index = i,
                    .InputCount = 0,
                    .ArgumentIndex = FuncArgs.Size,
                    .LastIndex = i + Output.Data[i].Size,
                    .PrevIndex = 0,
                };
                i++;
            }
        }
        
        // Applies bound variables in abstractions
        else {
            // Initializes a function without bound variables
            if (ResizeArray(&Funcs, (++Funcs.Size + 1) * sizeof (FuncStack))) goto CallFuncDefer;
            Funcs.Data[Funcs.Size] = (FuncStack) {
                .Index = i,
                .InputCount = 0,
                .ArgumentIndex = FuncArgs.Size,
                .LastIndex = i + Output.Data[i].Size,
                .PrevIndex = 0,
            };

            // Potential arguments of a free variable cannot reduce when evaluating arguments
            if (PostFreeVariable) {
                i++;
                continue;
            }
            
            // Potential arguments cannot reduce variables bound to other potential arguments
            PROFILE_NAMED("Abstraction evaluation");

            int MinF = 0;
            for (int j = i; j; j--)
                if (Output.Data[j].Size < 2) {
                    MinF = Funcs.Size - i + j + 1;
                    break;
                }

            int F = Funcs.Size; // Location of the last function that is a sentinel or not a grouping
            while (--F && Funcs.Data[F].PrevIndex == 0 && Funcs.Data[F].InputCount + Output.Data[Funcs.Data[F].Index].InputID == 0);
            if (MinF > F) F = MinF;

            for (int I = i; Output.Data[i].InputID;) {
                // Cannot update the current function with arguments of previously applied functions
                if (I + Output.Data[I].Size >= Funcs.Data[F].LastIndex) {
                    int ArgumentCount = 0;
                    int NextScope = 0;
                    if (F <= MinF) break;

                    do {
                        if (I + Output.Data[I].Size >= Funcs.Data[F].LastIndex) {
                            ArgumentCount += Funcs.Data[F].InputCount;

                            // Cannot apply arguments that do not exist or are outside the range of an known or potential argument
                            if (F == 0 || Funcs.Data[F].PrevIndex || Funcs.Data[F].InputCount == 0 && Output.Data[Funcs.Data[F].Index].InputID) {
                                NextScope = 1;
                                break;
                            }

                            // Finds location of the previous function that is a sentinel or not a grouping
                            while (--F && Funcs.Data[F].PrevIndex == 0 && Funcs.Data[F].InputCount + Output.Data[Funcs.Data[F].Index].InputID == 0);
                            continue;
                        }

                        // Updates the current argument index for past arguments
                        I += Output.Data[I].Size;
                        ArgumentCount--;
                    } while (ArgumentCount);

                    // There are no more applications for the current function
                    if (NextScope) break;
                    continue;
                }

                // Updates the current argument index and application counts
                I += Output.Data[I].Size;
                Output.Data[i].InputID--;
                Funcs.Data[Funcs.Size].InputCount++;

                // Appends the unreduced status to the argument buffer
                if (ResizeArray(&FuncArgs, (FuncArgs.Size + 1) * sizeof (FuncArg))) goto CallFuncDefer;
                FuncArgs.Data[FuncArgs.Size++] = (FuncArg) {
                    .IsReduced = 0,
                    .Index = I
                };
            }
            
            // Limits the parseing of functions with applications to terminate infinite recursion
            i++;
            if (Funcs.Data[Funcs.Size].InputCount && ++AbstractionsParsed >= MaxRecursionCount) goto CallFuncDefer;
            PROFILE_END();
        }
	}
    
    // Removes groupings following a sized term
	for (int i = 0; i < Output.Size;)
       	if ((i == 0 || Output.Data[i - 1].Size != 1) && Output.Data[i].Size != 1 && Output.Data[i].InputID == 0) {
        	Output.Size--;
        	for (int j = i; j < Output.Size; j++)
            	Output.Data[j] = Output.Data[j + 1];
          	 
           	for (int j = 0; j < i; j++)
            	if (Output.Data[j].Size > i - j)
                	Output.Data[j].Size--;
    	} else i++;
    
    // Combines abstractions when they end where the following abstraction ends
	for (int i = 0; i < Output.Size - 1;)
       	if (Output.Data[i + 1].Size != 1 && Output.Data[i].InputID && Output.Data[i + 1].InputID && Output.Data[i].Size - 1 == Output.Data[i + 1].Size) {
           	int StackIndex = 0;
            Abstractions.Data[0] = (Abstraction) {
                .ScopeOffset = 0,
                .OffsetEnd = i + Output.Data[i].Size
            };

            int TotalBounds = Output.Data[i].InputID + Output.Data[i + 1].InputID;
        	for (int j = i + 2; j < Output.Size; j++) {
                // Decreases the scope offset at the end of an abstraction
            	while (j >= Abstractions.Data[StackIndex].OffsetEnd)
            	    StackIndex--;
               	 
                // Decreases the bound ID for variables bound to the first abstraction and decreases it for those bound to the following one
                // For the reason that bound IDs are relative to the innermost abstraction
            	if (Output.Data[j].Size == 1 && Output.Data[j].InputID - Abstractions.Data[StackIndex].ScopeOffset < TotalBounds && Output.Data[j].InputID >= Abstractions.Data[StackIndex].ScopeOffset)
                    if (Output.Data[j].InputID - Abstractions.Data[StackIndex].ScopeOffset >= Output.Data[i + 1].InputID)
                        Output.Data[j].InputID -= Output.Data[i + 1].InputID;
                    else Output.Data[j].InputID += Output.Data[i].InputID;
                
                // Increases the scope offset when parseing an abstraction
            	else if (Output.Data[j].InputID) {
                    if (ResizeArray(&Abstractions, (++StackIndex + 1) * sizeof (Abstraction))) goto CallFuncDefer;
                	Abstractions.Data[StackIndex].ScopeOffset = Abstractions.Data[StackIndex - 1].ScopeOffset + Output.Data[j].InputID;
                	Abstractions.Data[StackIndex].OffsetEnd = j + Output.Data[j].Size;
            	}
        	}

            // Combines two abstraction terms into one
        	Output.Data[i].Size--;
        	Output.Data[i].InputID = TotalBounds;
   	 
            // Removes the remaining abstraction term
        	Output.Size--;
        	for (int j = i + 1; j < Output.Size; j++)
            	Output.Data[j] = Output.Data[j + 1];
          	 
           	for (int j = 0; j < i; j++)
            	if (Output.Data[j].Size > i - j)
                	Output.Data[j].Size--;
    	} else i++;
    
    ReturnValue = 0;

    // Frees memory buffers
    CallFuncDefer: 
    free(ReductionBuffer.Data);
    free(Abstractions.Data);
    free(FuncArgs.Data);
    free(Funcs.Data);

    // Returns the error code and output buffer
    *OutBuffer = Output;
    PROFILE_END();
    return ReturnValue;
}

int main(void) {
    PROFILE_SCOPE();
    FuncArray Output = {0};
    if (ResizeArray(&Output, StartBufferSize)) return 1;
    
    // Tests removing redundant groupings and abstractions
	Func ReduceGroupings [] = {{10, 0}, {1, 0}, {8, 1}, {7, 0}, {1, 2}, {5, 1}, {1, 3}, {3, 0}, {1, 4}, {1, 5}};
	CallFunc(ReduceGroupings, sizeof(ReduceGroupings) / sizeof(ReduceGroupings[0]), &Output);

	Func ReduceAbstractions [] = {{16, 3}, {15, 2}, {14, 2}, {1, 4}, {1, 3}, {1, 7}, {10, 2}, {1, 1}, {1, 6}, {1, 5}, {1, 9}, {5, 1}, {1, 0}, {1, 7}, {1, 6}, {1, 10}};
	CallFunc(ReduceAbstractions, sizeof(ReduceAbstractions) / sizeof(ReduceAbstractions[0]), &Output);

    // True = (λxy. x), False = (λxy. y)
	Func False [] = {{2, 2}, {1, 1}, {1, 0}, {3, 0}, {2, 2}, {1, 1}};
	CallFunc(False, sizeof(False) / sizeof(False[0]), &Output);

    // Not = (λp. p False True)
	Func Not [] = {{6, 1}, {1, 0}, {2, 2}, {1, 1}, {2, 2}, {1, 0}, {2, 2}, {1, 0}};
	CallFunc(Not, sizeof(Not) / sizeof(Not[0]), &Output);

    // Succ = (λnfx. f (n f x))
    // Zero = (λfx. x), One = (λfx. f x), Two = (λfx. f (f x))...
	Func Succ [32] = {{6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}};
	for (int i = 0; i < 7; i++) {
    	int j = 0;
    	for (; j < Output.Data[0].Size; j++)
        	Succ[6 + j] = Output.Data[j];
    	CallFunc(Succ, 6 + j, &Output);
	}
    
    // Plus = (λmn. m Succ n)
	Func Plus [] = {
    	{9, 2}, {1, 0}, {6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}, {1, 1},
    	{10, 2}, {1, 0}, {8, 0}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Plus, sizeof(Plus) / sizeof(Plus[0]), &Output);
    
    // Plus = (λmnfx. m f (n f x))
	Func Plus2 [] = {
    	{7, 4}, {1, 0}, {1, 2}, {4, 0}, {1, 1}, {1, 2}, {1, 3},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Plus2, sizeof(Plus2) / sizeof(Plus2[0]), &Output);
    
    // Mult = (λmn. m (PLUS n) 0)
	Func Times [] = {
    	{15, 2}, {1, 0}, {11, 0}, {9, 2}, {1, 0}, {6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}, {1, 1}, {1, 1}, {2, 2}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Times, sizeof(Times) / sizeof(Times[0]), &Output);
    
    // Mult = (λmnf. m (n f))
	Func Times2 [] = {
    	{5, 3}, {1, 0}, {3, 0}, {1, 1}, {1, 2},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Times2, sizeof(Times2) / sizeof(Times2[0]), &Output);

    // Pred = (λnfx. n (λgh. h (g f)) (λu. x) (λu. u))
    // Sub (n - m) = (λmn. m Pred n)
    Func Sub [] = {
        {14, 2}, {1, 0}, {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, {1, 1},
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
    	{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
    };
	CallFunc(Sub, sizeof(Sub) / sizeof(Sub[0]), &Output);

    // IsZero = (λn. n (λx. False) True)
    // Leq = (λmn. IsZero (Sub m n))
    // Equal = (λmn. Leq m n (Leq n m) False)
	Func Equal [] = {
	    {10, 3}, {1, 0}, {1, 1}, {1, 2}, {4, 0}, {1, 0}, {1, 2}, {1, 1}, {2, 2}, {1, 1},
	    {18, 2}, {1, 0}, {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, 
	    {1, 1}, {2, 3}, {1, 2}, {2, 2}, {1, 0},
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
		{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	};
	CallFunc(Equal, sizeof(Equal) / sizeof(Equal[0]), &Output);
	
    // Pair = (λxyf. f x y)
    // {} = Nil = False
    // {x} = (λf. f x)
    // {y x} = Pair y {x}
	
    // Tail = (λl. l (λhtd. t) False)
    // Skip = (λix. i Tail x)
	Func Skip [] = {
	    {9, 2}, {1, 0}, {6, 1}, {1, 0}, {2, 3}, {1, 1}, {2, 2}, {1, 1}, {1, 1},
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	    {12, 1}, {1, 0}, {1, 1}, {9, 1}, {1, 0}, {1, 2}, {6, 1}, {1, 0}, {1, 3}, {3, 1}, {1, 0}, {1, 4}
	};
	CallFunc(Skip, sizeof(Skip) / sizeof(Skip[0]), &Output);
	
	// Factorial = Y F
	// Y = (λg. (λx. g (x x)) (λx. g (x x)))
	// F = (λfn. (IsZero n) 1 (Mult n (f (Pred n))))
    Func Factorial [] = {
        {11, 1}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0},
        {34, 2}, {7, 1}, {1, 0}, {3, 1}, {2, 2}, {1, 1}, {2, 2}, {1, 0}, {1, 1}, {3, 2}, {1, 0}, {1, 1}, 
        {22, 0}, {5, 3}, {1, 0}, {3, 0}, {1, 1}, {1, 2}, {1, 1}, {15, 0}, {1, 0}, {13, 0}, 
        {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, {1, 1},
		{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
    };
	CallFunc(Factorial, sizeof(Factorial) / sizeof(Factorial[0]), &Output);
    
    // (x, y) = Pair x y
    // Factorial = (λn. n (λp. p (λabf. f (Mult a b) (Succ b))) (1, 1) True)
    Func Factorial2 [] = {
	    {27, 1}, {1, 0}, {15, 1}, {1, 0}, {13, 3}, {1, 2},
        {5, 1}, {1, 1}, {3, 0}, {1, 2}, {1, 0},
        {6, 2}, {1, 0}, {4, 0}, {1, 3}, {1, 0}, {1, 1},
	    {8, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 0},
		{11, 2}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	};
	CallFunc(Factorial2, sizeof(Factorial2) / sizeof(Factorial2[0]), &Output);
	
    // Fibonacci = (λn. n (λp. p (λabf. f (Plus a b) a)) (1, 0) True)
	Func Fibonacci [] = {
	    {23, 1}, {1, 0}, {12, 1}, {1, 0}, {10, 3}, {1, 2},
	    {7, 2}, {1, 2}, {1, 0}, {4, 0}, {1, 3}, {1, 0}, {1, 1}, {1, 0},
	    {7, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 1}, {2, 2}, {1, 0},
	    {13, 2}, {1, 0}, {11, 0}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
	};
	CallFunc(Fibonacci, sizeof(Fibonacci) / sizeof(Fibonacci[0]), &Output);

    // Div = (λcnmfx. (λd. IsZero d (Zero f x) (f (c d m f x))) (Sub n m))
    // Divide = (λn. Y div (Succ n))
    Func Divide [] = {
        {48, 1}, {11, 1}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0},
        {30, 5}, {15, 1}, {1, 0}, {2, 3}, {1, 2}, {2, 2}, {1, 0}, {1, 5},
        {8, 0}, {1, 4}, {6, 0}, {1, 1}, {1, 0}, {1, 3}, {1, 4}, {1, 5},
        {14, 0}, {1, 2}, {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, {1, 1},
        {6, 2}, {1, 0}, {4, 0}, {1, 2}, {1, 0}, {1, 1},
        {17, 0}, {9, 3}, {1, 1}, {7, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}, {1, 2}, {7, 2}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
        {7, 2}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
    };
	CallFunc(Divide, sizeof(Divide) / sizeof(Divide[0]), &Output);

    // Divide = (λmnfx. m (λrq. q r) (λq. x) (Y (λq. n (λqr. r q) (λr. f (r q)) (λx x))))
    Func Divide2 [] = {
        {31, 4}, {1, 0}, {3, 2}, {1, 1}, {1, 0}, {2, 1}, {1, 4}, {24, 0},
        {11, 1}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0},
        {12, 1}, {1, 2}, {3, 2}, {1, 1}, {1, 0}, {5, 1}, {1, 4}, {3, 0}, {1, 0}, {1, 1}, {2, 1}, {1, 0},
        {17, 0}, {9, 3}, {1, 1}, {7, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}, {1, 2}, {7, 2}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
        {7, 2}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
    };
	CallFunc(Divide2, sizeof(Divide2) / sizeof(Divide2[0]), &Output);

    PROFILE_END();
    return 0;
}
