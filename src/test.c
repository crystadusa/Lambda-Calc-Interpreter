#include "lambda.h"

void test() {
    PROFILE_SCOPE();
    FuncArray Output = {0};
    if (ResizeArray(&Output, START_BUFFER_SIZE)) return;
    
    // Tests removing redundant groupings and abstractions
	static Func ReduceGroupings [] = {{10, 0}, {1, 0}, {8, 1}, {7, 0}, {1, 2}, {5, 1}, {1, 3}, {3, 0}, {1, 4}, {1, 5}};
	CallFunc(ReduceGroupings, sizeof(ReduceGroupings) / sizeof(ReduceGroupings[0]), &Output, TEST_RECURSION_COUNT);

	static Func ReduceAbstractions [] = {{16, 3}, {15, 2}, {14, 2}, {1, 4}, {1, 3}, {1, 7}, {10, 2}, {1, 1}, {1, 6}, {1, 5}, {1, 9}, {5, 1}, {1, 0}, {1, 7}, {1, 6}, {1, 10}};
	CallFunc(ReduceAbstractions, sizeof(ReduceAbstractions) / sizeof(ReduceAbstractions[0]), &Output, TEST_RECURSION_COUNT);

    // True = (λxy. x), False = (λxy. y)
	static Func False [] = {{2, 2}, {1, 1}, {1, 0}, {3, 0}, {2, 2}, {1, 1}};
	CallFunc(False, sizeof(False) / sizeof(False[0]), &Output, TEST_RECURSION_COUNT);

    // Not = (λp. p False True)
	static Func Not [] = {{6, 1}, {1, 0}, {2, 2}, {1, 1}, {2, 2}, {1, 0}, {2, 2}, {1, 0}};
	CallFunc(Not, sizeof(Not) / sizeof(Not[0]), &Output, TEST_RECURSION_COUNT);

    // Succ = (λnfx. f (n f x))
    // Zero = (λfx. x), One = (λfx. f x), Two = (λfx. f (f x))...
	static Func Succ [32] = {{6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}};
	for (int i = 0; i < 7; i++) {
    	int j = 0;
    	for (; j < Output.Data[0].Size; j++)
        	Succ[6 + j] = Output.Data[j];
    	CallFunc(Succ, 6 + j, &Output, TEST_RECURSION_COUNT);
	}
    
    // Plus = (λmn. m Succ n)
	static Func Plus [] = {
    	{9, 2}, {1, 0}, {6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}, {1, 1},
    	{10, 2}, {1, 0}, {8, 0}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Plus, sizeof(Plus) / sizeof(Plus[0]), &Output, TEST_RECURSION_COUNT);
    
    // Plus = (λmnfx. m f (n f x))
	static Func Plus2 [] = {
    	{7, 4}, {1, 0}, {1, 2}, {4, 0}, {1, 1}, {1, 2}, {1, 3},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Plus2, sizeof(Plus2) / sizeof(Plus2[0]), &Output, TEST_RECURSION_COUNT);
    
    // Mult = (λmn. m (PLUS n) 0)
	static Func Times [] = {
    	{15, 2}, {1, 0}, {11, 0}, {9, 2}, {1, 0}, {6, 3}, {1, 1}, {4, 0}, {1, 0}, {1, 1}, {1, 2}, {1, 1}, {1, 1}, {2, 2}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{6, 2}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Times, sizeof(Times) / sizeof(Times[0]), &Output, TEST_RECURSION_COUNT);
    
    // Mult = (λmnf. m (n f))
	static Func Times2 [] = {
    	{5, 3}, {1, 0}, {3, 0}, {1, 1}, {1, 2},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1},
    	{8, 2}, {1, 0}, {6, 0}, {1, 0}, {4, 0}, {1, 0}, {2, 0}, {1, 1}
	};
	CallFunc(Times2, sizeof(Times2) / sizeof(Times2[0]), &Output, TEST_RECURSION_COUNT);

    // Pred = (λnfx. n (λgh. h (g f)) (λu. x) (λu. u))
    // Sub (n - m) = (λmn. m Pred n)
    static Func Sub [] = {
        {14, 2}, {1, 0}, {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, {1, 1},
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
    	{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
    };
	CallFunc(Sub, sizeof(Sub) / sizeof(Sub[0]), &Output, TEST_RECURSION_COUNT);

    // IsZero = (λn. n (λx. False) True)
    // Leq = (λmn. IsZero (Sub m n))
    // Equal = (λmn. Leq m n (Leq n m) False)
	static Func Equal [] = {
	    {10, 3}, {1, 0}, {1, 1}, {1, 2}, {4, 0}, {1, 0}, {1, 2}, {1, 1}, {2, 2}, {1, 1},
	    {18, 2}, {1, 0}, {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, 
	    {1, 1}, {2, 3}, {1, 2}, {2, 2}, {1, 0},
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
		{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	};
	CallFunc(Equal, sizeof(Equal) / sizeof(Equal[0]), &Output, TEST_RECURSION_COUNT);
	
    // Pair = (λxyf. f x y)
    // {} = Nil = False
    // {x} = (λf. f x)
    // {y x} = Pair y {x}
	
    // Tail = (λl. l (λhtd. t) False)
    // Skip = (λix. i Tail x)
	static Func Skip [] = {
	    {9, 2}, {1, 0}, {6, 1}, {1, 0}, {2, 3}, {1, 1}, {2, 2}, {1, 1}, {1, 1},
		{5, 2}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	    {12, 1}, {1, 0}, {1, 1}, {9, 1}, {1, 0}, {1, 2}, {6, 1}, {1, 0}, {1, 3}, {3, 1}, {1, 0}, {1, 4}
	};
	CallFunc(Skip, sizeof(Skip) / sizeof(Skip[0]), &Output, TEST_RECURSION_COUNT);
	
	// Factorial = Y F
	// Y = (λg. (λx. g (x x)) (λx. g (x x)))
	// F = (λfn. (IsZero n) 1 (Mult n (f (Pred n))))
    static Func Factorial [] = {
        {11, 1}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0},
        {34, 2}, {7, 1}, {1, 0}, {3, 1}, {2, 2}, {1, 1}, {2, 2}, {1, 0}, {1, 1}, {3, 2}, {1, 0}, {1, 1}, 
        {22, 0}, {5, 3}, {1, 0}, {3, 0}, {1, 1}, {1, 2}, {1, 1}, {15, 0}, {1, 0}, {13, 0}, 
        {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, {1, 1},
		{9, 2}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
    };
	CallFunc(Factorial, sizeof(Factorial) / sizeof(Factorial[0]), &Output, TEST_RECURSION_COUNT);
    
    // (x, y) = Pair x y
    // Factorial = (λn. n (λp. p (λabf. f (Mult a b) (Succ b))) (1, 1) True)
    static Func Factorial2 [] = {
	    {27, 1}, {1, 0}, {15, 1}, {1, 0}, {13, 3}, {1, 2},
        {5, 1}, {1, 1}, {3, 0}, {1, 2}, {1, 0},
        {6, 2}, {1, 0}, {4, 0}, {1, 3}, {1, 0}, {1, 1},
	    {8, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 0},
		{11, 2}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
	};
	CallFunc(Factorial2, sizeof(Factorial2) / sizeof(Factorial2[0]), &Output, TEST_RECURSION_COUNT);
	
    // Fibonacci = (λn. n (λp. p (λabf. f (Plus a b) a)) (1, 0) True)
	static Func Fibonacci [] = {
	    {23, 1}, {1, 0}, {12, 1}, {1, 0}, {10, 3}, {1, 2},
	    {7, 2}, {1, 2}, {1, 0}, {4, 0}, {1, 3}, {1, 0}, {1, 1}, {1, 0},
	    {7, 1}, {1, 0}, {3, 2}, {1, 0}, {1, 1}, {2, 2}, {1, 1}, {2, 2}, {1, 0},
	    {13, 2}, {1, 0}, {11, 0}, {1, 0}, {9, 0}, {1, 0}, {7, 0}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
	};
	CallFunc(Fibonacci, sizeof(Fibonacci) / sizeof(Fibonacci[0]), &Output, TEST_RECURSION_COUNT);

    // Div = (λcnmfx. (λd. IsZero d (Zero f x) (f (c d m f x))) (Sub n m))
    // Divide = (λn. Y div (Succ n))
    static Func Divide [] = {
        {48, 1}, {11, 1}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0},
        {30, 5}, {15, 1}, {1, 0}, {2, 3}, {1, 2}, {2, 2}, {1, 0}, {1, 5},
        {8, 0}, {1, 4}, {6, 0}, {1, 1}, {1, 0}, {1, 3}, {1, 4}, {1, 5},
        {14, 0}, {1, 2}, {11, 3}, {1, 0}, {5, 2}, {1, 1}, {3, 0}, {1, 0}, {1, 3}, {2, 1}, {1, 3}, {2, 1}, {1, 0}, {1, 1},
        {6, 2}, {1, 0}, {4, 0}, {1, 2}, {1, 0}, {1, 1},
        {17, 0}, {9, 3}, {1, 1}, {7, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}, {1, 2}, {7, 2}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
        {7, 2}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
    };
	CallFunc(Divide, sizeof(Divide) / sizeof(Divide[0]), &Output, TEST_RECURSION_COUNT);

    // Divide = (λmnfx. m (λrq. q r) (λq. x) (Y (λq. n (λqr. r q) (λr. f (r q)) (λx x))))
    static Func Divide2 [] = {
        {31, 4}, {1, 0}, {3, 2}, {1, 1}, {1, 0}, {2, 1}, {1, 4}, {24, 0},
        {11, 1}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0}, {5, 1}, {1, 1}, {3, 0}, {1, 0}, {1, 0},
        {12, 1}, {1, 2}, {3, 2}, {1, 1}, {1, 0}, {5, 1}, {1, 4}, {3, 0}, {1, 0}, {1, 1}, {2, 1}, {1, 0},
        {17, 0}, {9, 3}, {1, 1}, {7, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}, {1, 2}, {7, 2}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1},
        {7, 2}, {1, 0}, {5, 0}, {1, 0}, {3, 0}, {1, 0}, {1, 1}
    };
	CallFunc(Divide2, sizeof(Divide2) / sizeof(Divide2[0]), &Output, TEST_RECURSION_COUNT);

	free(Output.Data);
    PROFILE_END();
}
