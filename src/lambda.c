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

void UpdateFuncSize(Func* Output, FuncStack* Funcs, int FuncIndex, FuncArg* FuncArgs, int MaxArgIndex, int StartIndex, int SizeOffset) {
    PROFILE_SCOPE();

    // Updates sized terms
	for (int i = 0; i < StartIndex; i++)
		if (Output[i].Size > StartIndex - i)
			Output[i].Size += SizeOffset;

    // Updates function end positions
    for (int i = FuncIndex + 1; i;)
        if (Funcs[--i].LastIndex > StartIndex)
            Funcs[i].LastIndex += SizeOffset;

    // Updates argument positions
    for (int i = 0; i < MaxArgIndex; i++)
        if (FuncArgs[i].Index > StartIndex)
            FuncArgs[i].Index += SizeOffset;

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
	for (int i = 0; i < CalledCount; i++)
    	Output.Data[i] = Called[i];

    // Allocates memory buffers and returns on failure
    // Aside from FuncArgs, the size field is treated as the last index
    AbstractionArray Abstractions = {0};
    FuncArgArray FuncArgs = {0};
	FuncStackArray Funcs = {0};
    FuncArray ReductionBuffer = {0};
    if (ResizeArray(&Abstractions, START_BUFFER_SIZE) || ResizeArray(&FuncArgs, START_BUFFER_SIZE) ||
        ResizeArray(&Funcs, START_BUFFER_SIZE) || ResizeArray(&ReductionBuffer, START_BUFFER_SIZE)) goto CallFuncDefer;
    
    // Initializes a sentinel for function lookups
    Funcs.Data[0] = (FuncStack) {
        .Index = 0,
        .InputCount = 0,
        .ArgumentIndex = 0,
        .LastIndex = Output.Size,
        .PrevIndex = 0,
    };
	
	for (int i = 0; i < Output.Size || Funcs.Size;) {
        // Removes arguments and groupings after parsing a function
    	if (i >= Funcs.Data[Funcs.Size].LastIndex) {
            PROFILE_NAMED("Removing arguments");

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
             } while (F && Funcs.Data[F].PrevIndex == 0 && (AppliedOffset + ScopedOffset <= Output.Data[i].InputID || Funcs.Data[F].InputCount + Output.Data[Funcs.Data[F].Index].InputID == 0));
            ScopedOffset += AppliedOffset;

            // Detects sentinel values for unapplied bound variables and free variables
            int BoundID = Output.Data[i].InputID - ScopedOffset + Output.Data[Funcs.Data[F].Index].InputID + Funcs.Data[F].InputCount;
            if (F == 0 || Funcs.Data[F].PrevIndex || BoundID >= Funcs.Data[F].InputCount) {
                // Unapplied bound variables cannot be reduced so the applied variable count decreases their bound ID instead
                // Free variables do not need separate parsing when not evaluating arguments
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

                int ScopeF = F;
                for (int j = Funcs.Data[F].Index; j < i; j++) {
                    // Decreases the function index or scope offset at the end of an abstraction
                    while (ScopeF && j >= Funcs.Data[ScopeF].LastIndex) ScopeF--;
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
                        } while (F && Funcs.Data[F].PrevIndex == 0 && (ScopedOffset <= Output.Data[j].InputID || Funcs.Data[F].InputCount + Output.Data[Funcs.Data[F].Index].InputID == 0));

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
                
                // Increases the scope offset when parsing an abstraction
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
    PROFILE_FREE(ReductionBuffer.Data);
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
    int InFileSize = ftell(InFile);
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
