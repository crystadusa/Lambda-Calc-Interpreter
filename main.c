#define MaxBufferSize 16384
#define MaxFuncSize 4096
#define MaxStackSize 512
#define MaxRecursionSize 2048

typedef struct {
	int Size;
	int InputID;
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

void UpdateFuncSize(Func* Output, FuncStack* Funcs, int FuncIndex, FuncArg* FuncInputs, int MaxInputIndex, int FirstIndex, int SizeOffset) {	
	for (int i = 0; i < FirstIndex; i++)
		if (Output[i].Size > FirstIndex - i)
			Output[i].Size += SizeOffset;

    // Update last index values
    for (int i = FuncIndex + 1; i;)
        if (Funcs[--i].LastIndex > FirstIndex)
            Funcs[i].LastIndex += SizeOffset;

    // Update function input indicies
    for (int i = 0; i < MaxInputIndex; i++)
        if (FuncInputs[i].Index > FirstIndex)
            FuncInputs[i].Index += SizeOffset;
}

int CallFunc(Func* Called, int CalledCount, Func* Output) {
    if (CalledCount > MaxBufferSize) return 1;
	for (int i = 0; i < CalledCount; i++)
    	Output[i] = Called[i];

	int OutputSize = CalledCount;
    int AbstractionsParsed = 0;
    int InputOffsets[MaxStackSize];
    int OffsetEnds[MaxStackSize];

    int FuncInputIndex = 0;
    FuncArg FuncInputs [MaxFuncSize];

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
    	if (i >= Funcs[FuncIndex].LastIndex) {
            // Calculates end of empty groupings
            int F = FuncIndex;
            int EmptyGroupingCount = F;
            for (int Index = Funcs[FuncIndex].Index; --Index && Output[Index].Size > 1 && Output[Index].InputID + Funcs[F - 1].InputCount == 0 && i >= Index + Output[Index].Size; F--);
            EmptyGroupingCount -= F;

            // Calculates end of current empty grouping
            int SkippedGroupingCount = EmptyGroupingCount;
            int Index = Funcs[FuncIndex].Index;
            EmptyGroupingCount += Output[Index].Size > 1 && Output[Index].InputID == 0 && Output[Index].Size == 1 + Output[Index + 1].Size;

            int LastInputIndex = i;
            if (Funcs[FuncIndex].InputCount) {
                // Removes inputs from past functions
                LastInputIndex = FuncInputs[FuncInputIndex - 1].Index;
                for (int j = FuncIndex - 1; j && Funcs[j].PrevIndex == 0 && (Funcs[j].InputCount == 0 || FuncInputs[Funcs[j].ArgumentIndex].Index < LastInputIndex); j--)
                    Funcs[j].InputCount = 0;

                LastInputIndex += Output[LastInputIndex].Size;
                for (int j = i; j < LastInputIndex; j += Output[j].Size)
                    UpdateFuncSize(Output, Funcs, FuncIndex, FuncInputs, Funcs[FuncIndex].ArgumentIndex, i, -Output[j].Size);
            }

            // Removes empty groupings from output
            UpdateFuncSize(Output, Funcs, F, FuncInputs, FuncInputIndex, Funcs[F].Index, -EmptyGroupingCount);

            for (int j = Funcs[F].Index; j < i - EmptyGroupingCount; j++)
                Output[j] = Output[j + EmptyGroupingCount];

            // Removes inputs from output buffer
            i -= EmptyGroupingCount;
            for (int j = 0; j < OutputSize - LastInputIndex; j++)
                Output[i + j] = Output[LastInputIndex + j];

            OutputSize += i - LastInputIndex;
        
            if (Funcs[FuncIndex].PrevIndex) i = Funcs[FuncIndex].PrevIndex - 1;

            FuncIndex -= SkippedGroupingCount;
            FuncInputIndex = Funcs[--FuncIndex].ArgumentIndex + Funcs[FuncIndex].InputCount;
    	}
    	
    	else if (Output[i].Size < 2) {
            int F = FuncIndex + 1;
            int InputOffset = 0;
            int OutputOffset = 0;
            do {
                InputOffset += Funcs[--F].InputCount;
                OutputOffset += Output[Funcs[F].Index].InputID;
             } while (F && Funcs[F].PrevIndex == 0 && (InputOffset + OutputOffset <= Output[i].InputID || Funcs[F].InputCount + Output[Funcs[F].Index].InputID == 0));
            OutputOffset += InputOffset;

            int InputID = Output[i].InputID - OutputOffset + Output[Funcs[F].Index].InputID + Funcs[F].InputCount;
            if (F == 0 || Funcs[F].PrevIndex || InputID >= Funcs[F].InputCount) {
                Output[i++].InputID -= InputOffset;
                continue;
            }

            int InputIndex = FuncInputs[Funcs[F].ArgumentIndex + InputID].Index;
            if (FuncInputs[Funcs[F].ArgumentIndex + InputID].IsReduced == 0) {
                if (++FuncIndex >= MaxFuncSize) return 1;
                Funcs[FuncIndex] = (FuncStack) {
                    .Index = InputIndex,
                    .InputCount = 0,
                    .ArgumentIndex = FuncInputIndex,
                    .LastIndex = InputIndex + Output[InputIndex].Size,
                    .PrevIndex = i + 1,
                };

                FuncInputs[Funcs[F].ArgumentIndex + InputID].IsReduced = 1;
                i = InputIndex;
                continue;
            }

            // Skips functions without furthest input
            for (int j = F - 1; j && Funcs[j].PrevIndex == 0 && (Funcs[j].InputCount == 0 || FuncInputs[Funcs[j].ArgumentIndex].Index < InputIndex); j--)
                OutputOffset += Funcs[j].InputCount;

            int BufferIndex = 0;
            Func FuncBuffer [MaxBufferSize];

            int StackIndex = 0;
            InputOffsets[0] = 0;
            OffsetEnds[0] = InputIndex + Output[InputIndex].Size;

            int SizeOffset = Output[InputIndex].Size - 1;
            if (OutputSize + SizeOffset > MaxBufferSize) return 1;

            for (int j = InputIndex; j < InputIndex + Output[InputIndex].Size; j++) {
                while (j >= OffsetEnds[StackIndex])
                    StackIndex--;
                
                FuncBuffer[BufferIndex++] = Output[j];
                if (Output[j].Size == 1 && Output[j].InputID >= InputOffsets[StackIndex])
                    FuncBuffer[BufferIndex - 1].InputID += OutputOffset;
                
                else if (Output[j].InputID) {
                    if (++StackIndex >= MaxStackSize) return 1;
                    InputOffsets[StackIndex] = InputOffsets[StackIndex - 1] + Output[j].InputID;
                    OffsetEnds[StackIndex] = j + Output[j].Size;
                }
            }

            for (int j = 0; j < OutputSize - i - 1; j++)
                FuncBuffer[BufferIndex + j] = Output[i + 1 + j];

            OutputSize += SizeOffset;

            for (int j = i; j < OutputSize; j++)
                Output[j] = FuncBuffer[j - i];
        
            UpdateFuncSize(Output, Funcs, FuncIndex, FuncInputs, FuncInputIndex, i, SizeOffset);
    	}

        else if (Output[i].InputID == 0) {
            if (i < Funcs[FuncIndex].LastIndex - 1 && Output[i].Size - 1 == Output[i + 1].Size) {
                OutputSize--;
                for (int j = i; j < OutputSize; j++)
                    Output[j] = Output[j + 1];

                UpdateFuncSize(Output, Funcs, FuncIndex, FuncInputs, FuncInputIndex, i, -1);
            } else {
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
        
        else {
            if (++FuncIndex >= MaxFuncSize) return 1;
            Funcs[FuncIndex] = (FuncStack) {
                .Index = i,
                .InputCount = 0,
                .ArgumentIndex = FuncInputIndex,
                .LastIndex = i + Output[i].Size,
                .PrevIndex = 0,
            };

            int NextTerm = 0;
            for (int j = Funcs[FuncIndex - 1].Index; j < i; j++)
                if (Output[j].Size < 2) {
                    NextTerm = 1;
                    i++;
                    break;
                }
            if (NextTerm) continue;

            int F = FuncIndex; // Skips empty grouping's last index
            while (--F && Funcs[F].PrevIndex == 0 && Funcs[F].InputCount + Output[Funcs[F].Index].InputID == 0);
                
            for (int I = i; Output[i].InputID;) { // Removed Output[i].InputID--
                if (I + Output[I].Size >= Funcs[F].LastIndex) {
                    // Skips inputs of previously parsed functions
                    int ParsedInputs = 0;
                    do {
                        if (I + Output[I].Size >= Funcs[F].LastIndex) {
                            ParsedInputs += Funcs[F].InputCount;

                            // Cannot use inputs that don't exist or are out of range in an known or potential input
                            if (F == 0 || Funcs[F].PrevIndex || Funcs[F].InputCount == 0 && Output[Funcs[F].Index].InputID) {
                                NextTerm = 1;
                                break;
                            }

                            // Skips empty grouping's last index
                            while (--F && Funcs[F].PrevIndex == 0 && Funcs[F].InputCount + Output[Funcs[F].Index].InputID == 0);
                            continue;
                        }

                        I += Output[I].Size;
                        ParsedInputs--;
                    } while (ParsedInputs);

                    // Only stop when there is no available input
                    if (NextTerm) break;
                    continue;
                }

                I += Output[I].Size;
                Output[i].InputID--;
                Funcs[FuncIndex].InputCount++;

                if (FuncInputIndex >= MaxFuncSize) return 1;
                FuncInputs[FuncInputIndex++] = (FuncArg) {
                    .IsReduced = 0,
                    .Index = I
                };
            }
            
            i++;
            if (Funcs[FuncIndex].InputCount && ++AbstractionsParsed >= MaxRecursionSize) return 1;
        }
	}
    
	for (int i = 0; i < OutputSize;)
       	if ((i == 0 || Output[i - 1].Size != 1) && Output[i].Size != 1 && Output[i].InputID == 0) {
        	OutputSize--;
        	for (int j = i; j < OutputSize; j++)
            	Output[j] = Output[j + 1];
          	 
           	for (int j = 0; j < i; j++)
            	if (Output[j].Size > i - j)
                	Output[j].Size--;
    	} else i++;
    
	for (int i = 0; i < OutputSize - 1;)
       	if (Output[i + 1].Size != 1 && Output[i].InputID && Output[i + 1].InputID && Output[i].Size - 1 == Output[i + 1].Size) {
           	int StackIndex = 0;
        	InputOffsets[0] = 0;
        	OffsetEnds[0] = i + Output[i].Size;
       	 
            int TotalInputs = Output[i].InputID + Output[i + 1].InputID;
        	for (int j = i + 2; j < OutputSize; j++) {
            	while (j >= OffsetEnds[StackIndex])
            	    StackIndex--;
               	 
            	if (Output[j].Size == 1 && Output[j].InputID - InputOffsets[StackIndex] < TotalInputs && Output[j].InputID >= InputOffsets[StackIndex])
                    if (Output[j].InputID - InputOffsets[StackIndex] >= Output[i + 1].InputID)
                        Output[j].InputID -= Output[i + 1].InputID;
                    else Output[j].InputID += Output[i].InputID;
           	 
            	else if (Output[j].InputID) {
                	if (++StackIndex >= MaxStackSize) return 1;
                	InputOffsets[StackIndex] = InputOffsets[StackIndex - 1] + Output[j].InputID;
                	OffsetEnds[StackIndex] = j + Output[j].Size;
            	}
        	}

        	Output[i].Size--;
        	Output[i].InputID = TotalInputs;
   	 
        	OutputSize--;
        	for (int j = i + 1; j < OutputSize; j++)
            	Output[j] = Output[j + 1];
          	 
           	for (int j = 0; j < i; j++)
            	if (Output[j].Size > i - j)
                	Output[j].Size--;
    	} else i++;

	for (int i = OutputSize; i < MaxBufferSize; i++)
    	Output[i] = (Func) {0};
    	
    return 0;
}

int main() {
	Func Output [MaxBufferSize];
    
	Func ReduceGroupings [] = {{10, 0}, {1, 0}, {8, 1}, {7, 0}, {1, 2}, {5, 1}, {1, 3}, {3, 0}, {1, 4}, {1, 5}};
	CallFunc(ReduceGroupings, sizeof(ReduceGroupings) / sizeof(ReduceGroupings[0]), Output);

	Func ReduceAbstractions [] = {{16, 3}, {15, 2}, {14, 2}, {1, 4}, {1, 3}, {1, 7}, {10, 2}, {1, 1}, {1, 6}, {1, 5}, {1, 9}, {5, 1}, {1, 0}, {1, 7}, {1, 6}, {1, 10}};
	CallFunc(ReduceAbstractions, sizeof(ReduceAbstractions) / sizeof(ReduceAbstractions[0]), Output);

	Func False [] = {{2, 2}, {1, 1}, {1, 0}, {3, 0}, {2, 2}, {1, 1}};
	CallFunc(False, sizeof(False) / sizeof(False[0]), Output);

	Func Not [] = {{6, 1}, {1, 0}, {2, 2}, {1, 1}, {2, 2}, {1, 0}, {2, 2}, {1, 0}};
	CallFunc(Not, sizeof(Not) / sizeof(Not[0]), Output);

	Func Succ [MaxBufferSize] = {{6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}};
	for (int i = 0; i < 7; i++) {
    	int j = 0;
    	for (; j < Output[0].Size; j++)
        	Succ[6 + j] = Output[j];
    	CallFunc(Succ, 6 + j, Output);
	}
    
	Func Plus [] = {
    	{9, 2}, {1, 0}, {6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}, {1, 1},
    	{10, 2}, {1, 0}, {8, 0}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Plus, sizeof(Plus) / sizeof(Plus[0]), Output);
    
	Func Plus2 [] = {
    	{7, 4}, {1, 0}, {1, 2}, {4, 0}, {1, 1}, {1, 2}, {1, 3},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Plus2, sizeof(Plus2) / sizeof(Plus2[0]), Output);
    
	Func Times [] = {
    	{15, 2}, {1, 0}, {11, 0}, {9, 2}, {1, 0}, {6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}, {1, 1}, {1, 1}, {2, 2}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Times, sizeof(Times) / sizeof(Times[0]), Output);
    
	Func Times2 [] = {
    	{5, 3}, {1, 0}, {3, 0}, {1, 1}, {1, 2},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Times2, sizeof(Times2) / sizeof(Times2[0]), Output);

    Func Pred [] = {
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
        {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0},
    	{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
    };
	CallFunc(Pred, sizeof(Pred) / sizeof(Pred[0]), Output);
	
	Func Equal [] = {
	    {10, 3}, {1, 0}, {1, 1}, {1, 2}, {4, 0}, {1, 0}, {1, 2}, {1, 1}, {2, 2}, {1, 1},
	    {18, 2}, {1, 0}, {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, 
	    {1, 1}, {2, 3}, {1, 2}, {2, 2}, {1, 0},
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
		{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	};
	CallFunc(Equal, sizeof(Equal) / sizeof(Equal[0]), Output);
	
	Func Skip [] = {
	    {9, 2}, {1, 0}, {6, 1}, {1, 0}, {2, 3}, {1, 1}, {2, 2}, {1, 1}, {1, 1},
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	    {12, 1}, {1, 0}, {1, 1}, {9, 1}, {1, 0}, {1, 2}, {6, 1}, {1, 0}, {1, 3}, {3, 1}, {1, 0}, {1, 4}
	};
	CallFunc(Skip, sizeof(Skip) / sizeof(Skip[0]), Output);
	
	/*
	Factorial function = Y F
	    F = (λf. λn. (ISZERO n) 1 (MULT n (f (PRED n))))
	    ISZERO = λn.n (λx.FALSE) TRUE
        PRED := λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u)
	    Y = λg.(λx.g (x x)) (λx.g (x x))
    */

    Func Factorial [] = {
        {11, 1}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0},
        {34, 2}, {7, 1}, {1, 0}, {3, 1}, {2, 2}, {1, 1}, {2, 2}, {1, 0}, {1, 1}, {3, 2}, {1, 0}, {1, 1}, 
        {22, 0}, {5, 3}, {1, 0}, {3, 0}, {1, 1}, {1, 2}, {1, 1}, {15, 0}, {1, 0}, {13, 0}, 
        {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, {1, 1},
		{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
    };
	CallFunc(Factorial, sizeof(Factorial) / sizeof(Factorial[0]), Output);
	
	Func Factorial2 [] = {
	    {31, 1}, {1, 0}, {19, 2}, {1, 1}, 
	    {9, 1}, {1, 1}, {2, 2}, {1, 0}, {5, 0}, {1, 1}, {2, 2}, {1, 1}, {1, 0},
	    {8, 2}, {1, 0}, {6, 0}, {1, 2}, {2, 2}, {1, 1}, {1, 0}, {1, 1},
	    {8, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 0},
		{11, 2}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	};
	CallFunc(Factorial2, sizeof(Factorial2) / sizeof(Factorial2[0]), Output);
	
	Func Fibonacci [] = {
	    {28, 1}, {1, 0}, {17, 2}, {1, 1},
	    {11, 2}, {1, 2}, {2, 2}, {1, 0}, {1, 0}, {6, 0}, {1, 2}, {2, 2}, {1, 1}, {1, 0}, {1, 1},
	    {4, 0}, {1, 0}, {2, 2}, {1, 0},
	    {7, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 1}, {2, 2}, {1, 0},
	    {13, 2}, {1, 0}, {11, 0}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
	};
	CallFunc(Fibonacci, sizeof(Fibonacci) / sizeof(Fibonacci[0]), Output);
}
