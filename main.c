#define MaxFuncSize 16384
#define MaxStackSize 8192
#define MaxRecursionSize 2048

typedef struct {
	int Size;
	int InputID;
} Func;

typedef struct {
    int Index;
    int InputCount;
	int LastIndex;
	int PrevIndex;
} FuncStack;

void UpdateFuncSize(Func* Output, FuncStack* Funcs, int FuncIndex, int FirstIndex, int SizeOffset) {	
	for (int i = 0; i < FirstIndex; i++)
		if (Output[i].Size > FirstIndex - i)
			Output[i].Size += SizeOffset;
		
	for (int i = FuncIndex + 1; i;) {
		do {
			Funcs[--i].LastIndex += SizeOffset;
		} while (i && Funcs[i].PrevIndex == 0);
									
		while (Funcs[i].PrevIndex) {
			i -= Funcs[i].PrevIndex;
			Funcs[i].LastIndex += SizeOffset;
		}
	}
}

int CallFunc(Func* Called, int CalledCount, Func* Output) {
    if (CalledCount > MaxFuncSize) return 1;
	for (int i = 0; i < CalledCount; i++)
    	Output[i] = Called[i];

	int OutputSize = CalledCount;
    int AbstractionsParsed = 0;
    int InputOffsets[MaxStackSize];
    int OffsetEnds[MaxStackSize];

    int FuncIndex = 0;
	FuncStack Funcs [MaxStackSize];
    Funcs[0] = (FuncStack) {
        .Index = 0,
        .InputCount = 0,
        .LastIndex = OutputSize,
        .PrevIndex = 0,
    };
	
	for (int i = 0; i < OutputSize || FuncIndex;) {
    	if (i >= Funcs[FuncIndex].LastIndex) {
        	if (Funcs[FuncIndex--].PrevIndex)
            	i = Funcs[FuncIndex].Index;
        	continue;
    	}
    	
    	if (Output[i].Size < 2) {
        	i++;
        	continue;
    	}

    	if (Funcs[FuncIndex].InputCount == 0) {
        	if (Output[i].InputID == 0) {
            	if (i < Funcs[FuncIndex].LastIndex - 1 && Output[i].Size - 1 == Output[i + 1].Size) {
                	OutputSize--;
                	for (int j = i; j < OutputSize; j++)
                    	Output[j] = Output[j + 1];

					UpdateFuncSize(Output, Funcs, FuncIndex, i, -1);
            	} else {
                	if (++FuncIndex >= MaxStackSize) return 1;
                    Funcs[FuncIndex] = (FuncStack) {
                        .Index = i,
                        .InputCount = 0,
                        .LastIndex = i + Output[i].Size,
                        .PrevIndex = 0,
                    };
                	i++;
            	}
            	continue;
        	}
        	
        	int NextTerm = 0;
        	for (int j = Funcs[FuncIndex].Index; j < i; j++)
        	    if (Output[j].Size < 2) {
        	        NextTerm = 1;
        	        i++;
        	        break;
        	    }
        	if (NextTerm) continue;

           	if (++FuncIndex >= MaxStackSize) return 1;
            Funcs[FuncIndex] = (FuncStack) {
                .Index = i,
                .InputCount = 0,
                .LastIndex = Funcs[FuncIndex - 1].LastIndex,
                .PrevIndex = 0,
            };
           	 
        	int F = FuncIndex;
        	for (int I = i, j = 1; Output[I].InputID; Output[I].InputID--, j++) {
            	if (i + Output[i].Size >= Funcs[F].LastIndex) break;
            	i += Output[i].Size;
                Funcs[F].InputCount++;
                   	 
        	    if (++FuncIndex >= MaxStackSize) return 1;
                Funcs[FuncIndex] = (FuncStack) {
                    .Index = i,
                    .InputCount = 0,
                    .LastIndex = i + Output[i].Size,
                    .PrevIndex = j,
                };
            }
        	
        	if (Funcs[F].InputCount == 0) {
            	FuncIndex--;
            	i++;
        	}
        	else if (++AbstractionsParsed >= MaxRecursionSize) return 1;
        	continue;
    	}

    	Func FuncBuffer [MaxFuncSize];
    	int BufferIndex = 0;
    	int SizeOffset = 0;
    	int IsFuncNest = 0;
   	 
    	int StackIndex = 0;
    	InputOffsets[0] = 0;
    	OffsetEnds[0] = i + Output[i].Size;
    	
    	if (Output[i].InputID) FuncBuffer[BufferIndex++] = Output[i];
    	else SizeOffset--;

    	for (int j = i + 1; j < i + Output[i].Size; j++) {
        	while (j >= OffsetEnds[StackIndex])
            	StackIndex--;
       	 
           	if (Output[j].Size == 1) {
				int IsFound = 0;       	 
            	int InputIndex = i;
            	for (int k = 0; k < Funcs[FuncIndex].InputCount; k++) {
					InputIndex += Output[InputIndex].Size;
					
                	if (Output[j].InputID - InputOffsets[StackIndex] == k) {
                    	SizeOffset += Output[InputIndex].Size - 1;
                    	if (Output[i].Size + SizeOffset > MaxFuncSize) return 1;
                       	 
                       	int S = StackIndex;
                       	if (++StackIndex >= MaxStackSize) return 1;
                       	InputOffsets[StackIndex] = 0;
                    	OffsetEnds[StackIndex] = InputIndex + Output[InputIndex].Size;
                    	
                    	for (int l = 0; l < BufferIndex; l++)
                        	if (FuncBuffer[l].Size > BufferIndex - l)
                            	FuncBuffer[l].Size += Output[InputIndex].Size - 1;

                    	for (int l = InputIndex; l < InputIndex + Output[InputIndex].Size; l++) {
                    	    while (l >= OffsetEnds[StackIndex])
            	                StackIndex--;
                    	    
                        	FuncBuffer[BufferIndex++] = Output[l];
                        	if (Output[l].Size == 1) {
                        	    if (Output[l].InputID >= InputOffsets[StackIndex])
                            	    FuncBuffer[BufferIndex - 1].InputID += Output[i].InputID + InputOffsets[S];
                        	}
                        	
                        	else if (Output[l].InputID) {
                        	    if (++StackIndex >= MaxStackSize) return 1;
                            	InputOffsets[StackIndex] = InputOffsets[StackIndex - 1] + Output[l].InputID;
                            	OffsetEnds[StackIndex] = l + Output[l].Size;
                        	}
                    	}
                        
                        StackIndex = S;    
                        IsFound = 1;
                    	break;
                	}
            	}

				if (!IsFound) {
					FuncBuffer[BufferIndex++] = Output[j];
					if (Output[j].InputID >= InputOffsets[StackIndex])
						FuncBuffer[BufferIndex - 1].InputID -= Funcs[FuncIndex].InputCount;
				}
				continue;
        	}
       	 
			else if (Output[j].InputID) {
				if (++StackIndex >= MaxStackSize) return 1;
				InputOffsets[StackIndex] = InputOffsets[StackIndex - 1] + Output[j].InputID;
				OffsetEnds[StackIndex] = j + Output[j].Size;
			}
			FuncBuffer[BufferIndex++] = Output[j];
    	}

		int LastInputIndex = i;
		for (int j = 0; j <= Funcs[FuncIndex].InputCount; j++)
			LastInputIndex += Output[LastInputIndex].Size;
		SizeOffset -= LastInputIndex - i - Output[i].Size;

    	OutputSize += SizeOffset;
    	if (OutputSize > MaxFuncSize) return 1;
    	for (int j = 0; j < OutputSize - i - BufferIndex; j++)
        	FuncBuffer[BufferIndex + j] = Output[LastInputIndex + j];

		int EmptyGroupingCount = i;
    	Output[i].Size = FuncBuffer[0].Size - SizeOffset;
    	while (Output[i - 1].Size > 1 && Output[i - 1].InputID == 0 && Output[i - 1].Size - 1 == Output[i].Size) i--;
		EmptyGroupingCount -= i;

		OutputSize -= EmptyGroupingCount;
    	for (int j = i; j < OutputSize; j++)
        	Output[j] = FuncBuffer[j - i];

		UpdateFuncSize(Output, Funcs, FuncIndex - 1, i, SizeOffset - EmptyGroupingCount);
    	FuncIndex -= EmptyGroupingCount + 1;
	}
    
	for (int i = 0; i < OutputSize;)
       	if ((i == 0 || Output[i - 1].Size != 1 && Output[i - 1].InputID) && Output[i].Size != 1 && Output[i].InputID == 0) {
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
       	 
        	for (int j = i + 2; j < OutputSize; j++) {
            	while (j >= OffsetEnds[StackIndex])
            	    StackIndex--;
               	 
            	if (Output[j].Size == 1) {
                	if (Output[j].InputID - InputOffsets[StackIndex] < Output[i].InputID + Output[i + 1].InputID && Output[j].InputID >= InputOffsets[StackIndex])
                    	if (Output[j].InputID - InputOffsets[StackIndex] >= Output[i + 1].InputID)
                        	Output[j].InputID -= Output[i + 1].InputID;
                    	else Output[j].InputID += Output[i].InputID;
                	}
           	 
            	else if (Output[j].InputID) {
                	if (++StackIndex >= MaxStackSize) return 1;
                	InputOffsets[StackIndex] = InputOffsets[StackIndex - 1] + Output[j].InputID;
                	OffsetEnds[StackIndex] = j + Output[j].Size;
            	}
        	}

        	Output[i].Size--;
        	Output[i].InputID += Output[i + 1].InputID;
   	 
        	OutputSize--;
        	for (int j = i + 1; j < OutputSize; j++)
            	Output[j] = Output[j + 1];
          	 
           	for (int j = 0; j < i; j++)
            	if (Output[j].Size > i - j)
                	Output[j].Size--;
    	} else i++;

	for (int i = OutputSize; i < MaxFuncSize; i++)
    	Output[i] = (Func) {0};
    	
    return 0;
}

int main() {
	Func Output [MaxFuncSize];
    
	Func ReduceGroupings [] = {{10, 0}, {1, 0}, {8, 1}, {7, 0}, {1, 2}, {5, 1}, {1, 3}, {3, 0}, {1, 4}, {1, 5}};
	CallFunc(ReduceGroupings, sizeof(ReduceGroupings) / sizeof(ReduceGroupings[0]), Output);

	Func ReduceAbstractions [] = {{16, 3}, {15, 2}, {14, 2}, {1, 4}, {1, 3}, {1, 7}, {10, 2}, {1, 1}, {1, 6}, {1, 5}, {1, 9}, {5, 1}, {1, 0}, {1, 7}, {1, 6}, {1, 10}};
	CallFunc(ReduceAbstractions, sizeof(ReduceAbstractions) / sizeof(ReduceAbstractions[0]), Output);

	Func False [] = {{2, 2}, {1, 1}, {1, 0}, {3, 0}, {2, 2}, {1, 1}};
	CallFunc(False, sizeof(False) / sizeof(False[0]), Output);

	Func Not [] = {{6, 1}, {1, 0}, {2, 2}, {1, 1}, {2, 2}, {1, 0}, {2, 2}, {1, 0}};
	CallFunc(Not, sizeof(Not) / sizeof(Not[0]), Output);

	Func Succ [MaxFuncSize] = {{6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}};
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
	// F = (λf. λn. (ISZERO n) 1 (MULT n (f (PRED n))))
	// ISZERO = λn.n (λx.FALSE) TRUE
    // PRED := λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u)
	// Y = λg.(λx.g (x x)) (λx.g (x x))
	
	{11, 1}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0},
    {34, 2}, {7, 1}, {1, 0}, {3, 1}, {2, 2}, {1, 1}, {2, 2}, {1, 0}, {1, 1}, {3, 2}, {1, 0}, {1, 1}, 
    {22, 0}, {5, 3}, {1, 0}, {3, 0}, {1, 1}, {1, 2}, {1, 1}, {15, 0}, {1, 0}, {13, 0}, 
    {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, {1, 1},
    {2, 2}, {1, 0}
    */
	
	Func Factorial [] = {
	    {31, 1}, {1, 0}, {19, 2}, {1, 1}, 
	    {9, 1}, {1, 1}, {2, 2}, {1, 0}, {5, 0}, {1, 1}, {2, 2}, {1, 1}, {1, 0},
	    {8, 2}, {1, 0}, {6, 0}, {1, 2}, {2, 2}, {1, 1}, {1, 0}, {1, 1},
	    {8, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 0},
	    {15, 2}, {1, 0}, {13, 0}, {1, 0}, {11, 0}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
	};
	CallFunc(Factorial, sizeof(Factorial) / sizeof(Factorial[0]), Output);
	
	Func Fibonacci [] = {
	    {28, 1}, {1, 0}, {17, 2}, {1, 1},
	    {11, 2}, {1, 2}, {2, 2}, {1, 0}, {1, 0}, {6, 0}, {1, 2}, {2, 2}, {1, 1}, {1, 0}, {1, 1},
	    {4, 0}, {1, 0}, {2, 2}, {1, 0},
	    {7, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 1}, {2, 2}, {1, 0},
	    {13, 2}, {1, 0}, {11, 0}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
	};
	CallFunc(Fibonacci, sizeof(Fibonacci) / sizeof(Fibonacci[0]), Output);
}