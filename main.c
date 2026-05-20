// Includes and binds the tracy profiler for instrumentation
#ifdef TRACY_ENABLE
#include "dep/tracy/public/tracy/TracyC.h"
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

// Stack allocated space for each memory region
#define MaxBufferSize 16384
#define MaxFuncSize 4096
#define MaxStackSize 512
#define MaxRecursionSize 2048

// Data layout of custom types
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

static void UpdateFuncSize(Func* Output, FuncStack* Funcs, int FuncIndex, FuncArg* FuncInputs, int MaxInputIndex, int FirstIndex, int SizeOffset) {
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
        if (FuncInputs[i].Index > FirstIndex)
            FuncInputs[i].Index += SizeOffset;

    PROFILE_END();
}

static int CallFunc(Func* Called, int CalledCount, Func* Output) {
    PROFILE_NAMED("Lambda evaluation");

    // Copies the input buffer to the output buffer
    if (CalledCount > MaxBufferSize) return 1;
	for (int i = 0; i < CalledCount; i++)
    	Output[i] = Called[i];

	int OutputSize = CalledCount;
    int AbstractionsParsed = 0;
    int ScopeOffsets[MaxStackSize];
    int OffsetEnds[MaxStackSize];

    int FuncInputIndex = 0;
    FuncArg FuncInputs [MaxFuncSize];

    // Initializes a sentinel for function lookups
    int FuncIndex = 0;
	FuncStack Funcs [MaxFuncSize];
    Funcs[0] = (FuncStack) {
        .Index = 0,
        .InputCount = 0,
        .ArgumentIndex = 0,
        .LastIndex = OutputSize,
        .PrevIndex = 0,
    };
	
	for (int i = 0; i < OutputSize || FuncIndex;) {
        // Removes arguments and groupings after parseing a function
    	if (i >= Funcs[FuncIndex].LastIndex) {
            PROFILE_NAMED("Removeing arguments");

            // Calculates the number of preceding groupings ending before or at the end of the current function
            int F = FuncIndex;
            int GroupingCount = F;
            for (int Index = Funcs[FuncIndex].Index; --Index && Output[Index].Size > 1 && Output[Index].InputID + Funcs[F - 1].InputCount == 0 && i >= Index + Output[Index].Size; F--);
            GroupingCount -= F;

            // Calculates if the current function is now a grouping ending where the following sized term ends
            int FuncOffset = GroupingCount;
            int Index = Funcs[FuncIndex].Index;
            GroupingCount += Output[Index].Size > 1 && Output[Index].InputID == 0 && Output[Index].Size == 1 + Output[Index + 1].Size;

            int LastInputIndex = i;
            if (Funcs[FuncIndex].InputCount) {
                // Removes applied variables from earlier abstraction terms
                LastInputIndex = FuncInputs[FuncInputIndex - 1].Index;
                for (int j = FuncIndex - 1; j && Funcs[j].PrevIndex == 0 && (Funcs[j].InputCount == 0 || FuncInputs[Funcs[j].ArgumentIndex].Index < LastInputIndex); j--)
                    Funcs[j].InputCount = 0;

                // Updates size and positions from removing arguments
                LastInputIndex += Output[LastInputIndex].Size;
                for (int j = i; j < LastInputIndex; j += Output[j].Size)
                    UpdateFuncSize(Output, Funcs, FuncIndex, FuncInputs, Funcs[FuncIndex].ArgumentIndex, i, -Output[j].Size);
            }

            // Updates size and positions from removing groupings
            if (GroupingCount) UpdateFuncSize(Output, Funcs, F, FuncInputs, FuncInputIndex, Funcs[F].Index, -GroupingCount);

            // Removes groupings and arguments from the output buffer
            if (GroupingCount || i != LastInputIndex) {
                for (int j = Funcs[F].Index; j < i - GroupingCount; j++)
                    Output[j] = Output[j + GroupingCount];

                i -= GroupingCount;
                for (int j = 0; j < OutputSize - LastInputIndex; j++)
                    Output[i + j] = Output[LastInputIndex + j];

                OutputSize += i - LastInputIndex;
            }
        
            // Restores the previous parseing state
            if (Funcs[FuncIndex].PrevIndex) i = Funcs[FuncIndex].PrevIndex - 1;

            FuncIndex -= FuncOffset;
            FuncInputIndex = Funcs[--FuncIndex].ArgumentIndex + Funcs[FuncIndex].InputCount;
            PROFILE_END();
    	}
    	
        // Reduces bound variables
    	else if (Output[i].Size < 2) {
            // Determines the number of applied and unapplied variables
            // Stops counting when detecting a sentinel value or the current variable is bound to an abstraction
            int F = FuncIndex + 1;
            int AppliedOffset = 0;
            int ScopedOffset = 0;
            do {
                AppliedOffset += Funcs[--F].InputCount;
                ScopedOffset += Output[Funcs[F].Index].InputID;
             } while (F && Funcs[F].PrevIndex == 0 && (AppliedOffset + ScopedOffset <= Output[i].InputID || Funcs[F].InputCount + Output[Funcs[F].Index].InputID == 0));
            ScopedOffset += AppliedOffset;

            // Detects sentinel values for unapplied bound variables and free variables
            // These cannot be reduced so the applied variable count decreases their bound ID instead
            int BoundID = Output[i].InputID - ScopedOffset + Output[Funcs[F].Index].InputID + Funcs[F].InputCount;
            if (F == 0 || Funcs[F].PrevIndex || BoundID >= Funcs[F].InputCount) {
                Output[i++].InputID -= AppliedOffset;
                continue;
            }

            // The lazy reduction strategy parses arguments right before reduction
            int ArgumentIndex = FuncInputs[Funcs[F].ArgumentIndex + BoundID].Index;
            if (FuncInputs[Funcs[F].ArgumentIndex + BoundID].IsReduced == 0) {
                // The previous index is a sentinel that stores the reduction position
                if (++FuncIndex >= MaxFuncSize) return 1;
                Funcs[FuncIndex] = (FuncStack) {
                    .Index = ArgumentIndex,
                    .InputCount = 0,
                    .ArgumentIndex = FuncInputIndex,
                    .LastIndex = ArgumentIndex + Output[ArgumentIndex].Size,
                    .PrevIndex = i + 1,
                };

                // Marks the selected argument as reduced before parsing
                FuncInputs[Funcs[F].ArgumentIndex + BoundID].IsReduced = 1;
                i = ArgumentIndex;
                continue;
            }

            // Arguments applied to previous abstractions are skipped on the next reduction by updating the scoped argument count
            PROFILE_NAMED("Bound variable evaluation");
            for (int j = F - 1; j && Funcs[j].PrevIndex == 0 && (Funcs[j].InputCount == 0 || FuncInputs[Funcs[j].ArgumentIndex].Index < ArgumentIndex); j--)
                ScopedOffset += Funcs[j].InputCount;

            // Applies a beta reduction
            int BufferIndex = 0;
            Func ReductionBuffer [MaxBufferSize];

            int StackIndex = 0;
            ScopeOffsets[0] = 0;
            OffsetEnds[0] = ArgumentIndex + Output[ArgumentIndex].Size;

            int SizeOffset = Output[ArgumentIndex].Size - 1;
            if (OutputSize + SizeOffset > MaxBufferSize) return 1;

            for (int j = ArgumentIndex; j < ArgumentIndex + Output[ArgumentIndex].Size; j++) {
                // Decreases the scope offset at the end of an abstraction
                while (j >= OffsetEnds[StackIndex])
                    StackIndex--;

                // Use the scoped argument count to increase bound IDs for variables that are free or bounded outside the current abstraction
                ReductionBuffer[BufferIndex++] = Output[j];
                if (Output[j].Size == 1 && Output[j].InputID >= ScopeOffsets[StackIndex])
                    ReductionBuffer[BufferIndex - 1].InputID += ScopedOffset;
                
                // Increases the scope offset when parseing an abstraction
                else if (Output[j].InputID) {
                    if (++StackIndex >= MaxStackSize) return 1;
                    ScopeOffsets[StackIndex] = ScopeOffsets[StackIndex - 1] + Output[j].InputID;
                    OffsetEnds[StackIndex] = j + Output[j].Size;
                }
            }

            // Moves a term to the reduction position for when the argument is only one term long
            Output[i] = ReductionBuffer[0];

            if (SizeOffset) {
                // Appends the output buffer at the reduction position to the reduction buffer
                for (int j = 0; j < OutputSize - i - 1; j++)
                    ReductionBuffer[BufferIndex + j] = Output[i + 1 + j];

                OutputSize += SizeOffset;

                // Moves the reduction buffer to the output buffer at the reduction position
                for (int j = i + 1; j < OutputSize; j++)
                    Output[j] = ReductionBuffer[j - i];
            
                UpdateFuncSize(Output, Funcs, FuncIndex, FuncInputs, FuncInputIndex, i, SizeOffset);
            }
            PROFILE_END();
    	}

        // Parses groupings
        else if (Output[i].InputID == 0) {
            if (i < Funcs[FuncIndex].LastIndex - 1 && Output[i].Size - 1 == Output[i + 1].Size) {
                PROFILE_NAMED("Grouping evaluation");

                // Removes groupings when they end where the following sized term ends
                OutputSize--;
                for (int j = i; j < OutputSize; j++)
                    Output[j] = Output[j + 1];

                UpdateFuncSize(Output, Funcs, FuncIndex, FuncInputs, FuncInputIndex, i, -1);
                PROFILE_END();
            } else {
                // Handles groupings as a function
                if (++FuncIndex >= MaxFuncSize) return 1;
                Funcs[FuncIndex] = (FuncStack) {
                    .Index = i,
                    .InputCount = 0,
                    .ArgumentIndex = FuncInputIndex,
                    .LastIndex = i + Output[i].Size,
                    .PrevIndex = 0,
                };
                i++;
            }
        }
        
        // Applies bound variables in abstractions
        else {
            // Initializes a function without bound variables
            if (++FuncIndex >= MaxFuncSize) return 1;
            Funcs[FuncIndex] = (FuncStack) {
                .Index = i,
                .InputCount = 0,
                .ArgumentIndex = FuncInputIndex,
                .LastIndex = i + Output[i].Size,
                .PrevIndex = 0,
            };

            // Potential arguments cannot reduce bound variables
            int NextTerm = 0;
            for (int j = Funcs[FuncIndex - 1].Index; j < i; j++)
                if (Output[j].Size < 2) {
                    NextTerm = 1;
                    i++;
                    break;
                }

            if (NextTerm) continue;
            PROFILE_NAMED("Abstraction evaluation");

            int F = FuncIndex; // Location of the last function that is a sentinel or not a grouping
            while (--F && Funcs[F].PrevIndex == 0 && Funcs[F].InputCount + Output[Funcs[F].Index].InputID == 0);
                
            for (int I = i; Output[i].InputID;) {
                // Cannot update the current function with arguments of previously applied functions
                if (I + Output[I].Size >= Funcs[F].LastIndex) {
                    int ArgumentCount = 0;
                    do {
                        if (I + Output[I].Size >= Funcs[F].LastIndex) {
                            ArgumentCount += Funcs[F].InputCount;

                            // Cannot apply arguments that do not exist or are outside the range of an known or potential argument
                            if (F == 0 || Funcs[F].PrevIndex || Funcs[F].InputCount == 0 && Output[Funcs[F].Index].InputID) {
                                NextTerm = 1;
                                break;
                            }

                            // Finds location of the previous function that is a sentinel or not a grouping
                            while (--F && Funcs[F].PrevIndex == 0 && Funcs[F].InputCount + Output[Funcs[F].Index].InputID == 0);
                            continue;
                        }

                        // Updates the current argument index for past arguments
                        I += Output[I].Size;
                        ArgumentCount--;
                    } while (ArgumentCount);

                    // There are no more applications for the current function
                    if (NextTerm) break;
                    continue;
                }

                // Updates the current argument index and application counts
                I += Output[I].Size;
                Output[i].InputID--;
                Funcs[FuncIndex].InputCount++;

                // Appends the unreduced status to the argument buffer
                if (FuncInputIndex >= MaxFuncSize) return 1;
                FuncInputs[FuncInputIndex++] = (FuncArg) {
                    .IsReduced = 0,
                    .Index = I
                };
            }
            
            // Limits the parseing of functions with applications to terminate infinite recursion
            i++;
            if (Funcs[FuncIndex].InputCount && ++AbstractionsParsed >= MaxRecursionSize) return 1;
            PROFILE_END();
        }
	}
    
    // Removes groupings following a sized term
	for (int i = 0; i < OutputSize;)
       	if ((i == 0 || Output[i - 1].Size != 1) && Output[i].Size != 1 && Output[i].InputID == 0) {
        	OutputSize--;
        	for (int j = i; j < OutputSize; j++)
            	Output[j] = Output[j + 1];
          	 
           	for (int j = 0; j < i; j++)
            	if (Output[j].Size > i - j)
                	Output[j].Size--;
    	} else i++;
    
    // Combines abstractions when they end where the following abstraction ends
	for (int i = 0; i < OutputSize - 1;)
       	if (Output[i + 1].Size != 1 && Output[i].InputID && Output[i + 1].InputID && Output[i].Size - 1 == Output[i + 1].Size) {
           	int StackIndex = 0;
        	ScopeOffsets[0] = 0;
        	OffsetEnds[0] = i + Output[i].Size;
       	 
            int TotalBounds = Output[i].InputID + Output[i + 1].InputID;
        	for (int j = i + 2; j < OutputSize; j++) {
                // Decreases the scope offset at the end of an abstraction
            	while (j >= OffsetEnds[StackIndex])
            	    StackIndex--;
               	 
                // Decreases the bound ID for variables bound to the first abstraction and decreases it for those bound to the following one
                // For the reason that bound IDs are relative to the innermost abstraction
            	if (Output[j].Size == 1 && Output[j].InputID - ScopeOffsets[StackIndex] < TotalBounds && Output[j].InputID >= ScopeOffsets[StackIndex])
                    if (Output[j].InputID - ScopeOffsets[StackIndex] >= Output[i + 1].InputID)
                        Output[j].InputID -= Output[i + 1].InputID;
                    else Output[j].InputID += Output[i].InputID;
                
                // Increases the scope offset when parseing an abstraction
            	else if (Output[j].InputID) {
                	if (++StackIndex >= MaxStackSize) return 1;
                	ScopeOffsets[StackIndex] = ScopeOffsets[StackIndex - 1] + Output[j].InputID;
                	OffsetEnds[StackIndex] = j + Output[j].Size;
            	}
        	}

            // Combines two abstraction terms into one
        	Output[i].Size--;
        	Output[i].InputID = TotalBounds;
   	 
            // Removes the remaining abstraction term
        	OutputSize--;
        	for (int j = i + 1; j < OutputSize; j++)
            	Output[j] = Output[j + 1];
          	 
           	for (int j = 0; j < i; j++)
            	if (Output[j].Size > i - j)
                	Output[j].Size--;
    	} else i++;

    // Fills the remaining output buffer with null terms
	for (int i = OutputSize; i < MaxBufferSize; i++)
    	Output[i] = (Func) {0};
    	
    PROFILE_END();
    return 0; // Returns no error code
}

int main(void) {
    PROFILE_SCOPE();
	Func Output [MaxBufferSize];
    
    // Tests removing redundant groupings and abstractions
	Func ReduceGroupings [] = {{10, 0}, {1, 0}, {8, 1}, {7, 0}, {1, 2}, {5, 1}, {1, 3}, {3, 0}, {1, 4}, {1, 5}};
	CallFunc(ReduceGroupings, sizeof(ReduceGroupings) / sizeof(ReduceGroupings[0]), Output);

	Func ReduceAbstractions [] = {{16, 3}, {15, 2}, {14, 2}, {1, 4}, {1, 3}, {1, 7}, {10, 2}, {1, 1}, {1, 6}, {1, 5}, {1, 9}, {5, 1}, {1, 0}, {1, 7}, {1, 6}, {1, 10}};
	CallFunc(ReduceAbstractions, sizeof(ReduceAbstractions) / sizeof(ReduceAbstractions[0]), Output);

    // True = (λxy. x), False = (λxy. y)
	Func False [] = {{2, 2}, {1, 1}, {1, 0}, {3, 0}, {2, 2}, {1, 1}};
	CallFunc(False, sizeof(False) / sizeof(False[0]), Output);

    // Not = (λp. p False True)
	Func Not [] = {{6, 1}, {1, 0}, {2, 2}, {1, 1}, {2, 2}, {1, 0}, {2, 2}, {1, 0}};
	CallFunc(Not, sizeof(Not) / sizeof(Not[0]), Output);

    // Succ = (λnfx. f (n f x))
    // Zero = (λfx. x), One = (λfx. f x), Two = (λfx. f (f x))...
	Func Succ [MaxBufferSize] = {{6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}};
	for (int i = 0; i < 7; i++) {
    	int j = 0;
    	for (; j < Output[0].Size; j++)
        	Succ[6 + j] = Output[j];
    	CallFunc(Succ, 6 + j, Output);
	}
    
    // Plus = (λmn. m Succ n)
	Func Plus [] = {
    	{9, 2}, {1, 0}, {6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}, {1, 1},
    	{10, 2}, {1, 0}, {8, 0}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Plus, sizeof(Plus) / sizeof(Plus[0]), Output);
    
    // Plus = (λmnfx. m f (n f x))
	Func Plus2 [] = {
    	{7, 4}, {1, 0}, {1, 2}, {4, 0}, {1, 1}, {1, 2}, {1, 3},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Plus2, sizeof(Plus2) / sizeof(Plus2[0]), Output);
    
    // Mult = (λmn. m (PLUS n) 0)
	Func Times [] = {
    	{15, 2}, {1, 0}, {11, 0}, {9, 2}, {1, 0}, {6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}, {1, 1}, {1, 1}, {2, 2}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Times, sizeof(Times) / sizeof(Times[0]), Output);
    
    // Mult = (λmnf. m (n f))
	Func Times2 [] = {
    	{5, 3}, {1, 0}, {3, 0}, {1, 1}, {1, 2},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Times2, sizeof(Times2) / sizeof(Times2[0]), Output);

    // Pred = (λnfx. n (λgh. h (g f)) (λu. x) (λu. u))
    // Sub (m - n) = (λmn. m Pred n)
    Func Pred [] = {
        {14, 2}, {1, 0}, {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, {1, 1},
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
    	{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
    };
	CallFunc(Pred, sizeof(Pred) / sizeof(Pred[0]), Output);

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
	CallFunc(Equal, sizeof(Equal) / sizeof(Equal[0]), Output);
	
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
	CallFunc(Skip, sizeof(Skip) / sizeof(Skip[0]), Output);
	
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
	CallFunc(Factorial, sizeof(Factorial) / sizeof(Factorial[0]), Output);
    
    // (x, y) = Pair x y
    // Factorial = (λn. n (λp. p (λabf. f (Mult a b) (Succ b))) (1, 1) True)
    Func Factorial2 [] = {
	    {27, 1}, {1, 0}, {15, 1}, {1, 0}, {13, 3}, {1, 2},
        {5, 1}, {1, 1}, {3, 0}, {1, 2}, {1, 0},
        {6, 2}, {1, 0}, {4, 0}, {1, 3}, {1, 0}, {1, 1},
	    {8, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 0},
		{11, 2}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	};
	CallFunc(Factorial2, sizeof(Factorial2) / sizeof(Factorial2[0]), Output);
	
    // Fibonacci = (λn. n (λp. p (λabf. f (Plus a b) a)) (1, 0) True)
	Func Fibonacci [] = {
	    {23, 1}, {1, 0}, {12, 1}, {1, 0}, {10, 3}, {1, 2},
	    {7, 2}, {1, 2}, {1, 0}, {4, 0}, {1, 3}, {1, 0}, {1, 1}, {1, 0},
	    {7, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 1}, {2, 2}, {1, 0},
	    {13, 2}, {1, 0}, {11, 0}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
	};
	CallFunc(Fibonacci, sizeof(Fibonacci) / sizeof(Fibonacci[0]), Output);
    PROFILE_END();
}
