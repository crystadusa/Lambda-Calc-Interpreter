# Crystadusa's lambda calculus interpreter 
### About
This project uses a custom format for [lambda expressions](https://en.wikipedia.org/wiki/Lambda_calculu) and reduces them to normal form. The [lazy reduction strategy](https://sookocheff.com/post/fp/evaluating-lambda-expressions/) is used to prevent arguments from being evaluated more than once and avoids recursion by only evaluating them when needed. I plan to implement further optimizations and I/O via the command line.

### Data Format
Each term has a size followed by an input id. Terms with a size of one are variables where the input id determines if it is free or which abstraction it is bound to. The first abstraction of the innermost function had an id of zero, which is followed by its subsequent abstractions, and then the next most inner function. Sized terms with an input id of zero are groupings which prioritize the order of reductions. When not a potential argument of a free variable nor evaluating an argument, reductions are evaluated inside them. Functions have an abstraction count equal to the input id and apply arguments to internal variables bound to their abstractions; beta reductions.

### Configuration
* StartBufferSize: Initial size of memory buffers in bytes
* MaxRecursionCount: Limit on evaluating functions with applications before terminating

### Build
This project has both a make and cmake build system.

To build this project with make enter this command in the .build directory.
* make clean all BUILD=[Release, Debug]

To build this project with unix make files enter the following commands in the top directory.
1. cmake --fresh -S .build -B build -G "Unix Makefiles" -DCMAKE_BUILD_TYPE=[RELEASE, DEBUG]
2. cmake --build build

To build this project with msvc enter the following commands in the top directory.
1. cmake --fresh -S .build -B build -G "Visual Studio 17 2022"
2. cmake --build build --config [Release, Debug]

Defining TRACY to 1 for make or ON for cmake builds with the tracy profiler for instrumentation\
Defining CC for make determines the c compiler and CMAKE_[C, CXX]_COMPILER_ID for cmake determines the [c, c++] compiler\
Defining ASSEMBLY_FILE to main for cmake will assemble main.s for msvc, and gcc/clang when targeting asm
