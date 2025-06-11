#define MaxFuncSize 64

typedef struct {
	int size;
	int inCount;
} Func;

int AppendFuncs(Func** Inputs, int InputCount, Func* Output) {
	int OutputIndex = 0;
	int FirstIn = 0;
	for (int i = 0; i < InputCount; i++) {
    	int NextIn = 0;
    	for (int j = 0; j < Inputs[i]->size; j++) {
        	if (Inputs[i][j].inCount > NextIn)
            	NextIn = Inputs[i][j].inCount;

        	Output[OutputIndex] = Inputs[i][j];
        	Output[OutputIndex++].inCount += FirstIn;
    	}
    	FirstIn += NextIn + 1;
	}

	return OutputIndex;
}

void CallFunc(Func* Called, int CalledCount, Func* Output) {
	for (int i = 0; i < CalledCount; i++)
    	Output[i] = Called[i];

	int OutputSize = CalledCount;
	for (int i = 0; i < OutputSize;) {
    	if (Output[i].size < 2 || Output[i].size >= OutputSize - i) {
        	i++;
        	continue;
    	}

    	Func FuncBuffer [MaxFuncSize];
    	Func* SubInput = Output + i + Output[i].size;

    	int OutputIndex = i;
    	for (int j = i + 1; j < i + Output[i].size; j++) {
        	if (Output[j].inCount == Output[i].inCount) {
            	OutputSize += SubInput->size - 1;
            	for (int k = i; k < OutputIndex; k++)
                	if (FuncBuffer[k].size > OutputIndex - k)
                    	FuncBuffer[k].size += SubInput->size - 1;

            	FuncBuffer[i].size += Output[j].size - 1;
            	for (int k = 0; k < SubInput->size; k++)
                	FuncBuffer[OutputIndex++] = SubInput[k];
        	}
        	else {
            	FuncBuffer[OutputIndex++] = Output[j];
            	//OutputIndex += Output[j].size;
        	}
    	}

    	OutputSize -= SubInput->size + 1;
    	int NextInputIndex = i + Output[i].size + SubInput->size;
    	for (int j = 0; j < OutputSize - OutputIndex; j++)
        	FuncBuffer[OutputIndex + j] = Output[NextInputIndex + j];

    	for (int j = 0; j < i; j++)
        	if (Output[j].size > OutputIndex - j)
            	Output[j].size -= SubInput->size + 1;

    	for (int j = i; j < OutputSize; j++)
        	Output[j] = FuncBuffer[j];
	}

	for (int i = OutputSize; i < MaxFuncSize; i++)
    	Output[i] = (Func) {0};
}

int main() {
    /*
	Func True [] = {{3, 0}, {2, 1}, {1, 0}};
	Func False [] = {{3, 0}, {2, 1}, {1, 1}};
	Func Not [MaxFuncSize] = {{2, 0}, {1, 0}};

	Func* Inputs [] = {Not, False, True};
	Not->size = AppendFuncs(Inputs, 3, Not);

	Inputs[1] = True;
	int NotCount = AppendFuncs(Inputs, 2, Not);

	Func Output [MaxFuncSize];
	CallFunc(Not, NotCount, Output);
    */

	Func Number [MaxFuncSize] = {{3, 0}, {2, 1}, {1, 1}};
	Func Succ [MaxFuncSize] = {{7, 0}, {6, 1}, {5, 2}, {1, 1}, {1, 0}, {1, 1}, {1, 2}};

	Func* Inputs [] = {Succ, Number};

	for (int i = 0; i < 7; i ++) {
    	int CallCount = AppendFuncs(Inputs, 2, Succ);
    	CallFunc(Succ, CallCount, Number);
	}

    /*
	Func Two [] = {{5, 0}, {4, 1}, {3, 0}, {2, 0}, {1, 1}};
	Func Three [] = {{6, 0}, {5, 1}, {4, 0}, {3, 0}, {2, 0}, {1, 1}};
	Func Plus [MaxFuncSize] = {{9, 0}, {1, 0}, {7, 1}, {6, 2}, {5, 3}, {1, 2}, {1, 1}, {1, 2}, {1, 3}};

	Func* Inputs [] = {Plus, Two, Three};
	int CallCount = AppendFuncs(Inputs, 3, Plus);

	Func Output [MaxFuncSize];
	CallFunc(Plus, CallCount, Output);
    */
}