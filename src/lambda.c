#include "lambda.h"

int ResizeArray(void* DynArray, int Size) {
    Array* Data = (Array*) 1;
    Array* Array = DynArray;
    if (Array->Capacity < Size) {
        // Doubles capacity or until it can hold the new size
        PROFILE_SCOPE();
        Array->Capacity *= 2;
        if (Array->Capacity < Size) Array->Capacity = Size;

        // Reallocates memory into a larger buffer
        PROFILE_FREE(Array->Data);
        Data = realloc(Array->Data, Array->Capacity);

        if (Data) {
            Array->Data = Data;
            PROFILE_ALLOC(Data, Array->Capacity);
        } 
        PROFILE_END();
    }

    // Returns an error code if realloc fails
    return Data ? 0 : 1;
}

void UpdateFuncSize(Func* Output, int StartIndex, int SizeOffset) {
    // Updates sized terms
    PROFILE_SCOPE();
	for (int i = 0; i < StartIndex; i++)
		if (Output[i].Size > StartIndex - i)
			Output[i].Size += SizeOffset;

    PROFILE_END();
}

int CallFunc(Func* Called, int CalledCount, FuncArray* OutBuffer, int MaxRecursionCount) {
    PROFILE_NAMED("Lambda evaluation");
    
    int ReturnValue = 1;
    int AbstractionsParsed = 0;
    int PostFreeVariable = 0;

    // Resizes the output buffer to fit the input buffer
    FuncArray Output = *OutBuffer;
    if (ResizeArray(&Output, CalledCount * sizeof (Func))) return 1;
    Output.Size = CalledCount;

    // Copies the input buffer to the output buffer
    memcpy(Output.Data, Called, CalledCount * sizeof (Func));

    // Allocates memory buffers and returns on failure
    // Aside from FuncArgs, the size field is treated as the last index
    AbstractionArray Abstractions = {0};
    FuncArgArray FuncArgs = {0};
	FuncStackArray Funcs = {0};
    if (ResizeArray(&Abstractions, START_BUFFER_SIZE) || ResizeArray(&FuncArgs, START_BUFFER_SIZE) || ResizeArray(&Funcs, START_BUFFER_SIZE)) goto CallFuncDefer;
    
    // Initializes a sentinel for function lookups
    Funcs.Data[0] = (FuncStack) {.PrevIndex = 1};
	
	for (int i = 0; i < Output.Size || Funcs.Size;) {
        // Removes arguments and groupings after parsing a function
    	if (Funcs.Size && i >= Funcs.Data[Funcs.Size].Index + Output.Data[Funcs.Data[Funcs.Size].Index].Size) {
            PROFILE_NAMED("Removing arguments");

            int LastInputIndex = i;
            if (Funcs.Data[Funcs.Size].InputCount) {
                // Removes applied variables from earlier abstraction terms
                LastInputIndex = Funcs.Data[Funcs.Size].Index;
                for (int j = 0; j < FuncArgs.Data[FuncArgs.Size - 1].Offset; j++)
                    LastInputIndex += Output.Data[LastInputIndex].Size;

                for (int j = Funcs.Size - 1; Funcs.Data[j].PrevIndex == 0; j--) {
                    int Index = Funcs.Data[j].Index;
                    for (int k = 0; k < FuncArgs.Data[Funcs.Data[k].ArgumentIndex].Offset; k++)
                        Index += Output.Data[Index].Size;

                    if (Index >= LastInputIndex) break;
                    Funcs.Data[j].InputCount = 0;
                } 

                // Updates size and positions from removing arguments
                LastInputIndex += Output.Data[LastInputIndex].Size;
                for (int j = i; j < LastInputIndex; j += Output.Data[j].Size)
                    UpdateFuncSize(Output.Data, i, -Output.Data[j].Size);
            }

            // Calculates the number of preceding groupings ending before or at the end of the current function
            int GroupingCount = 0;            
            int FuncOffset = 0;
            int UpdateIndex = Funcs.Data[Funcs.Size].Index;
            for (int F = Funcs.Size;; GroupingCount++, UpdateIndex--) {
                if (Output.Data[UpdateIndex - 1].Size < 2 || Output.Data[UpdateIndex - 1].InputID) break;
                if (UpdateIndex - 1 == Funcs.Data[F - 1].Index && Funcs.Data[F - 1].InputCount) break;
                if (i < UpdateIndex - 1 + Output.Data[UpdateIndex - 1].Size) break;

                if (UpdateIndex - 1 == Funcs.Data[F - 1].Index && Funcs.Data[F - 1].PrevIndex == 0) {
                    F--;
                    FuncOffset++;
                }
            }

            // Calculates if the current function is now a grouping ending where the following sized term ends
            int Index = Funcs.Data[Funcs.Size].Index;
            GroupingCount += Output.Data[Index].Size > 1 && Output.Data[Index].InputID == 0 && Output.Data[Index].Size == 1 + Output.Data[Index + 1].Size;

            // Updates size and positions from removing groupings
            if (GroupingCount) UpdateFuncSize(Output.Data, UpdateIndex, -GroupingCount);

            // Removes groupings and arguments from the output buffer
            if (GroupingCount || i != LastInputIndex) {
                i -= GroupingCount;
                memmove(Output.Data + UpdateIndex, Output.Data + UpdateIndex + GroupingCount, (i - UpdateIndex) * sizeof (Func));
                memmove(Output.Data + i, Output.Data + LastInputIndex, (Output.Size - LastInputIndex) * sizeof (Func));

                Output.Size += i - LastInputIndex;
            }
        
            // Restores the previous parsing state
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
             } while (Funcs.Data[F].PrevIndex == 0 && AppliedOffset + ScopedOffset <= Output.Data[i].InputID);
            ScopedOffset += AppliedOffset;

            // Detects sentinel values for unapplied bound variables and free variables
            int BoundID = Output.Data[i].InputID - ScopedOffset + Output.Data[Funcs.Data[F].Index].InputID + Funcs.Data[F].InputCount;
            if (Funcs.Data[F].PrevIndex || BoundID >= Funcs.Data[F].InputCount) {
                // Unapplied bound variables cannot be reduced so the applied variable count decreases their bound ID instead
                // Free variables do not need separate parsing when not evaluating arguments
                if (F == 0 || Funcs.Data[F].PrevIndex == 0) {
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

                // Free variables may later become bound when evaluating arguments
                // So Input IDs must be updated to remove potential arguments from functions
                int StackIndex = 0;
                Abstractions.Data[0] = (Abstraction) {
                    .ScopeOffset = 0,
                    .OffsetEnd = i
                };

                int ScopeF = F;
                for (int j = Funcs.Data[F].Index; j < i; j++) {
                    // Decreases the function index or scope offset at the end of an abstraction
                    while (ScopeF && j >= Funcs.Data[ScopeF].Index + Output.Data[Funcs.Data[ScopeF].Index].Size) ScopeF--;
                    while (j >= Abstractions.Data[StackIndex].OffsetEnd) StackIndex--;

                    // Tracks the most recent function to later sum their input counts
                    // Increases the scope offset when parsing an abstraction
                    if (ScopeF < LastF && Funcs.Data[ScopeF + 1].Index == j) ScopeF++;
                    else if (Output.Data[j].Size > 1 && Output.Data[j].InputID) {
                        if (ResizeArray(&Abstractions, (++StackIndex + 1) * sizeof (Abstraction))) goto CallFuncDefer;
                        Abstractions.Data[StackIndex].ScopeOffset = Abstractions.Data[StackIndex - 1].ScopeOffset + Output.Data[j].InputID;
                        Abstractions.Data[StackIndex].OffsetEnd = j + Output.Data[j].Size;
                    }

                    if (Output.Data[j].Size == 1 && Output.Data[j].InputID >= Abstractions.Data[StackIndex].ScopeOffset) {
                        // Stops counting potential inputs when detecting a sentinel value or the current variable is bound to an abstraction
                        int F = ScopeF + 1;
                        int AppliedOffset = 0;
                        int ScopedOffset = Abstractions.Data[StackIndex].ScopeOffset;
                        do {
                            AppliedOffset += Funcs.Data[--F].InputCount;
                            ScopedOffset += Output.Data[Funcs.Data[F].Index].InputID;
                        } while (Funcs.Data[F].PrevIndex == 0 && ScopedOffset <= Output.Data[j].InputID);

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
            int ArgumentIndex = Funcs.Data[F].Index;
            for (int j = 0; j < FuncArgs.Data[Funcs.Data[F].ArgumentIndex + BoundID].Offset; j++)
                ArgumentIndex += Output.Data[ArgumentIndex].Size;

            if (FuncArgs.Data[Funcs.Data[F].ArgumentIndex + BoundID].IsReduced == 0) {
                // The previous index is a sentinel that stores the reduction position
                if (ResizeArray(&Funcs, (++Funcs.Size + 1) * sizeof (FuncStack))) goto CallFuncDefer;
                Funcs.Data[Funcs.Size] = (FuncStack) {
                    .Index = ArgumentIndex,
                    .InputCount = 0,
                    .ArgumentIndex = FuncArgs.Size,
                    .PrevIndex = i + 1,
                };

                // Marks the selected argument as reduced before parsing
                FuncArgs.Data[Funcs.Data[F].ArgumentIndex + BoundID].IsReduced = 1;
                i = ArgumentIndex;
                continue;
            }

            // Variables free to arguments need to skip arguments applied to previous abstractions so the scoped argument count is updated
            PROFILE_NAMED("Bound variable evaluation");
            for (int j = F - 1; Funcs.Data[j].PrevIndex == 0; j--) {
                int Index = Funcs.Data[j].Index;
                for (int k = 0; k < FuncArgs.Data[Funcs.Data[k].ArgumentIndex].Offset; k++)
                    Index += Output.Data[Index].Size;

                if (Index >= ArgumentIndex) break;
                ScopedOffset += Funcs.Data[j].InputCount;
            } 

            // Resizes the output buffer to fit the reduced argument
            int SizeOffset = Output.Data[ArgumentIndex].Size - 1;
            if (ResizeArray(&Output, (Output.Size + SizeOffset) * sizeof (Func))) goto CallFuncDefer;
            ArgumentIndex += SizeOffset;

            // Shifts all terms after the reduction position to fit the reduced argument
            PROFILE_CONTEXT("memmove", __memmove);
            if (SizeOffset) memmove(Output.Data + i + SizeOffset, Output.Data + i, (Output.Size - i) * sizeof (Func));
            PROFILE_END_CONTEXT(__memmove);

            // Applies a beta reduction
            int ReductionIndex = i;
            int StackIndex = 0;
            Abstractions.Data[0] = (Abstraction) {
                .ScopeOffset = 0,
                .OffsetEnd = ArgumentIndex + Output.Data[ArgumentIndex].Size
            };

            for (int j = ArgumentIndex; j < ArgumentIndex + Output.Data[ArgumentIndex].Size; j++) {
                // Decreases the scope offset at the end of an abstraction
                while (j >= Abstractions.Data[StackIndex].OffsetEnd)
                    StackIndex--;

                // Use the scoped argument count to increase bound IDs for variables that are free or bounded outside the current abstraction
                Output.Data[ReductionIndex++] = Output.Data[j];
                if (Output.Data[j].Size == 1 && Output.Data[j].InputID >= Abstractions.Data[StackIndex].ScopeOffset)
                    Output.Data[ReductionIndex - 1].InputID += ScopedOffset;
                
                // Increases the scope offset when parsing an abstraction
                else if (Output.Data[j].InputID) {
                    if (ResizeArray(&Abstractions, (++StackIndex + 1) * sizeof (Abstraction))) goto CallFuncDefer;
                    Abstractions.Data[StackIndex].ScopeOffset = Abstractions.Data[StackIndex - 1].ScopeOffset + Output.Data[j].InputID;
                    Abstractions.Data[StackIndex].OffsetEnd = j + Output.Data[j].Size;
                }
            }

            // Updates size and positions from applying a beta reduction
            Output.Size += SizeOffset;            
            if (SizeOffset) UpdateFuncSize(Output.Data, i, SizeOffset);
            PROFILE_END();
    	}

        // Parses groupings
        else if (Output.Data[i].InputID == 0) {
            if (i < Output.Size - 1 && Output.Data[i].Size - 1 == Output.Data[i + 1].Size) {
                // Removes groupings when they end where the following sized term ends
                PROFILE_NAMED("Grouping evaluation");
                Output.Size--;
                memmove(Output.Data + i, Output.Data + i + 1, (Output.Size - i) * sizeof (Func));

                UpdateFuncSize(Output.Data, i, -1);
                PROFILE_END();
            } else i++;
        }
        
        // Applies bound variables in abstractions
        else {
            // Initializes a function without bound variables
            if (ResizeArray(&Funcs, (++Funcs.Size + 1) * sizeof (FuncStack))) goto CallFuncDefer;
            Funcs.Data[Funcs.Size] = (FuncStack) {
                .Index = i,
                .InputCount = 0,
                .ArgumentIndex = FuncArgs.Size,
                .PrevIndex = 0,
            };

            // Potential arguments of a free variable cannot reduce when evaluating arguments
            if (PostFreeVariable) {
                i++;
                continue;
            }
            
            // Potential arguments cannot reduce variables bound to other potential arguments
            // The index of the sized term bounding the argument search is capped at the previous variable
            PROFILE_NAMED("Abstraction evaluation");

            int MaxIndex = INT_MAX;
            for (int j = i; j; j--)
                if (Output.Data[j].Size < 2) {
                    MaxIndex = j + 1;
                    MaxIndex += Output.Data[MaxIndex].Size;
                    break;
                }

            int F = Funcs.Size - 1;
            int SearchIndex = Funcs.Data[F].Index;
            SearchIndex += Output.Data[SearchIndex].Size;

            if (MaxIndex < SearchIndex) {
                F++;
                SearchIndex = MaxIndex;
            }

            for (int I = i, Offset = 0; Output.Data[i].InputID;) {
                // Cannot update the current function with arguments of previously applied functions
                if (F == 0 ? I + Output.Data[I].Size >= Output.Size : I + Output.Data[I].Size >= SearchIndex) {
                    int ArgumentCount = 0;
                    int NextScope = 0;
                    if (SearchIndex >= MaxIndex) break;

                    do {
                        if (F == 0 ? I + Output.Data[I].Size >= Output.Size : I + Output.Data[I].Size >= SearchIndex) {
                            ArgumentCount += Funcs.Data[F].InputCount;
                            Offset += Funcs.Data[F].InputCount;

                            // Cannot apply arguments that do not exist or are outside the range of an known or potential argument
                            if (Funcs.Data[F].InputCount == 0) {
                                NextScope = 1;
                                break;
                            }

                            // Updates the search index with the previous function
                            SearchIndex = Funcs.Data[--F].Index;
                            SearchIndex += Output.Data[SearchIndex].Size;
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
                    .Offset = ++Offset
                };
            }
            
            // Limits the parsing of functions with applications to terminate infinite recursion
            i++;
            if (Funcs.Data[Funcs.Size].InputCount && ++AbstractionsParsed >= MaxRecursionCount) goto CallFuncDefer;
            PROFILE_END();
        }
	}
    
    // Removes groupings following a sized term
	for (int i = 0; i < Output.Size;)
       	if ((i == 0 || Output.Data[i - 1].Size != 1) && Output.Data[i].Size != 1 && Output.Data[i].InputID == 0) {
        	Output.Size--;
            memmove(Output.Data + i, Output.Data + i + 1, (Output.Size - i) * sizeof (Func));
          	 
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
                
                // Increases the scope offset when parsing an abstraction
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
            memmove(Output.Data + i + 1, Output.Data + i + 2, (Output.Size - i - 1) * sizeof (Func));
          	 
           	for (int j = 0; j < i; j++)
            	if (Output.Data[j].Size > i - j)
                	Output.Data[j].Size--;
    	} else i++;
    
    ReturnValue = 0;

    // Frees memory buffers
    CallFuncDefer: 
    free(Abstractions.Data);
    free(FuncArgs.Data);
    free(Funcs.Data);
    PROFILE_FREE(Abstractions.Data);
    PROFILE_FREE(FuncArgs.Data);
    PROFILE_FREE(Funcs.Data);

    // Returns the error code and output buffer
    *OutBuffer = Output;
    PROFILE_END();
    return ReturnValue;
}

// OutChars must be a buffer at least a MAX_INT_CHARS character long
int IntToChars(char* OutChars, int InNum) {
    // Determines the number of decimal digits in an integer
    int Num = InNum;
    int Digits = 1;
    while (Num > 9) {
        Digits++;
        Num /= 10;
    }

    // Writes the decimal digits to a string buffer
    Num = InNum;
    for (int j = Digits; j > 0;) {
        OutChars[--j] = '0' + (char) (Num % 10);
        Num /= 10;
    }

    // Returns the number of digits written
    return Digits;
}

// TODO file and lambda validation
int main(int argc, char** argv) {
    // Reads the input and output file paths
    char* InFilePath = 0;
    char* OutFilePath = 0;

    int IsBinaryMode = 0;
    int InFileIsBinary = 0;
    int OutFileIsBinary = 0;

    int StopArguments = 0;
    int MaxRecursionCount = 4096;

    static char HelpStr [] = "\n"
        "lambda <InFilePath> <OutFilePath>\n"
        "Options:\n"
        "    -b, -binary         Reads next file as an array of numeric terms in binary.\n"
        "    -r, -recurse <Max>  Limit on evaluating functions with arguments before terminating.\n"
        "    -t, -text           Reads next file as text with numeric terms separated by white space.\n"
        "    --                  Reads remaining arguments as file paths.";

    for (int i = 1; i < argc; i++) {
        if (argv[i][0] == '-' && StopArguments == 0) {
            // Parse the next file as binary or text
            if (argv[i][1] == 'b' || argv[i][1] == 'B') IsBinaryMode = 1;
            else if (argv[i][1] == 't' || argv[i][1] == 'T') IsBinaryMode = 0;

            // '--' makes all the following arguments file paths
            else if (argv[i][1] == '-') StopArguments = 1;

            // Parses the number after '-r' as the max recursion count
            else if (argv[i][1] == 'r' || argv[i][1] == 'R') {
                MaxRecursionCount = 0;
                if (argv[i][2] >= '0' && argv[i][2] <= '9') {
                    int j = 2;
                    do {
                        int Overflow = 0;
                        if (OVERFLOW_MUL_I32(MaxRecursionCount, 10)) Overflow = 1;
                        if (OVERFLOW_ADD_I32(MaxRecursionCount, argv[i][j] - '0')) Overflow = 1;

                        j++;
                        if (Overflow) {
                            MaxRecursionCount = INT_MAX;
                            break;
                        }
                    } while (argv[i][j] >= '0' && argv[i][j] <= '9');
                }

                // Parses the next argument as a number when one was not after '-r'
                else if (++i < argc && argv[i][0] >= '0' && argv[i][0] <= '9') {
                    int j = 0;
                    do {
                        int Overflow = 0;
                        if (OVERFLOW_MUL_I32(MaxRecursionCount, 10)) Overflow = 1;
                        if (OVERFLOW_ADD_I32(MaxRecursionCount, argv[i][j] - '0')) Overflow = 1;

                        j++;
                        if (Overflow) {
                            MaxRecursionCount = INT_MAX;
                            break;
                        }
                    } while (argv[i][j] >= '0' && argv[i][j] <= '9');
                }

                // Returns error when no number is found
                else {
                    puts("Error: Recursion limit is unspecified");
                    puts(HelpStr);
                    return 1;
                }
            }

            // Terminates for unrecognized option
            else {
                puts("Error: Unrecognized command line argument");
                puts(HelpStr);
                return 1;
            }
        }

        // Reads the next file path
        else if (InFilePath == 0) {
            InFilePath = argv[i];
            InFileIsBinary = IsBinaryMode;
            IsBinaryMode = 0;
        }
        
        else if (OutFilePath == 0) {
            OutFilePath = argv[i];
            OutFileIsBinary = IsBinaryMode;
            IsBinaryMode = 0;
        }
    }

    // Display error if there are not enough command line argument
    if (InFilePath == 0 || OutFilePath == 0) {
        puts("Error: Two files must be entered");
        puts(HelpStr);
        return 1;
    }

    // Opens the input file
    FILE* InFile = fopen(InFilePath, "rb");
    if (InFile == 0) {
        puts("Error: File path is not valid");
        return 1;
    }

    // Determines the size of the input file
    if (fseek(InFile, 0, SEEK_END) == -1) goto MainDefer;
    int InFileSize = (int) ftell(InFile);
    if (InFileSize == -1) goto MainDefer;
    rewind(InFile);

    // Allocates memory to read the input file
    char* FileMem = malloc(InFileSize);
    PROFILE_ALLOC(FileMem, InFileSize);
    if (FileMem == 0) goto MainDefer;
    
    if (fread(FileMem, 1, InFileSize, InFile) != (size_t) InFileSize) goto MainDefer;

    // Converts byte units to term units for binary inputs
    int* TermMem;
    int TermCount = 0;
    if (InFileIsBinary) {
        TermMem = (int*) FileMem;
        TermCount = InFileSize / sizeof (int);
    }

    // Parses text with numbers separated by white space as lambda terms
    else {
        TermMem = malloc(InFileSize * sizeof (int));
        PROFILE_ALLOC(TermMem, InFileSize * sizeof (int));

        for (int i = 0;;) {
            while (i < InFileSize && (FileMem[i] < '0' || FileMem[i] > '9')) i++;
            if (i >= InFileSize) break;

            // Parses each digit of a number and stores the result
            int Term = 0;
            do {
                int Overflow = 0;
                if (OVERFLOW_MUL_I32(Term, 10)) Overflow = 1;
                if (OVERFLOW_ADD_I32(Term, FileMem[i] - '0')) Overflow = 1;

                i++;
                if (Overflow) {
                    puts("Error: Term is greater than the 32 bit signed integer limit");
                    return 1;
                }
            } while (i < InFileSize && FileMem[i] >= '0' && FileMem[i] <= '9');

            TermMem[TermCount++] = Term;
        }
    }

    // Reduces the lambda function to normal form
    FuncArray Output = {0};
    if (ResizeArray(&Output, START_BUFFER_SIZE)) goto MainDefer;

    if (CallFunc((Func*) TermMem, TermCount / 2, &Output, MaxRecursionCount)) {
        puts("Error: Failed to reduce function to normal form");
        return 1;
    }

    // Opens the output file
    FILE* OutFile = fopen(OutFilePath, "wb");
    if (OutFile == 0) goto MainDefer;

    // Writes the reduced form to the output file
    if (OutFileIsBinary) fwrite(Output.Data, sizeof (Func), Output.Size, OutFile);

    // Converts lambda terms into a string with two numbers surrounded by parenthesis
    else for (int i = 0; i < Output.Size; i++) {
        char Write [MAX_INT_CHARS * 2 + 4];
        Write[0] = '(';

        int Offset = IntToChars(Write + 1, Output.Data[i].Size);
        Write[Offset + 1] = ' ';

        Offset += IntToChars(Write + Offset + 2, Output.Data[i].InputID);

        Write[Offset + 2] = ')';
        Write[Offset + 3] = ' ';
        fwrite(Write, 1, Offset + 4, OutFile);
    }

    // Acknowledges successful beta reduction and file write
    puts("Wrote the reduced form to the output file");
    return 0;

    MainDefer:
    puts("Error: Failed unexpectedly");
    return 1;
}
