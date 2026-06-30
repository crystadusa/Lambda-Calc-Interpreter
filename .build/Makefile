# Directories and lists of files by type
SRC_DIR := ../src
BLD_DIR := ../build
DEP_DIR := ../dep

SRCS := $(wildcard $(SRC_DIR)/*.c)
OBJS := $(patsubst $(SRC_DIR)/%.c,$(BLD_DIR)/%.o,$(SRCS))
EXEC := lambda

# Compilation flags
ASMFLAGS := -masm=intel -fverbose-asm -fno-lto
CFLAGS := -MMD -MP -isystem $(DEP_DIR) -Wall -Wextra -pedantic -Wconversion -Wdouble-promotion -Wno-parentheses -Wno-sign-conversion -Wno-unused-function
LDFLAGS := -w

TRACY_LDFLAGS := -lstdc++

# Detects compiler
CC ?= gcc
ifneq ($(findstring clang,$(CC)),)
    LDFLAGS += -fuse-ld=lld
else
    TRACY_LDFLAGS += -lgcc_s
endif

# Detects operating system
ifeq ($(OS), Windows_NT)
    EXEC = lambda.exe
    LDFLAGS += -lkernel32
    TRACY_LDFLAGS += -ldbghelp -lsecur32 -lws2_32
endif

# Adds compilation flags based on build type
ifndef BUILD
    BUILD = Debug
endif

ifeq ($(BUILD), Release)
    CFLAGS += -O2 -flto=auto
    LDFLAGS += -flto -s
else ifeq ($(BUILD), Debug)
    CFLAGS += -g
else
    $(error Build type "$(BUILD)" is not valid)
endif

# Flag to build with the tracy profiler
ifeq ($(TRACY), 1)
    OBJS += $(BLD_DIR)/TracyClient.o
    CFLAGS += -DTRACY_ENABLE -DTRACY_NO_EXIT -fno-omit-frame-pointer
    LDFLAGS += $(TRACY_LDFLAGS)
endif

# Includes dependencies
DEPS := $(OBJS:.o=.d)
-include $(DEPS)

# Target for the final executable
all: $(BLD_DIR)/$(EXEC)

# Makes the build directory if it does not exist
$(BLD_DIR):
	@mkdir -p $@

# Compiles source files into the target
$(BLD_DIR)/$(EXEC): $(OBJS) | $(BLD_DIR)
	$(CC) $^ $(LDFLAGS) -o $@

# Compiles c code into object files
$(BLD_DIR)/%.o: $(SRC_DIR)/%.c | $(BLD_DIR)
	$(CC) $(CFLAGS) -c $< -o $@

# Assembles c code into assembly code
%.s: $(BLD_DIR)/%.s;
$(BLD_DIR)/%.s: $(SRC_DIR)/%.c | $(BLD_DIR)
	$(CC) $(CFLAGS) $(ASMFLAGS) -S $< -o $@

# Compiles TracyClient.cpp without warnings
$(BLD_DIR)/TracyClient.o: $(DEP_DIR)/tracy/public/TracyClient.cpp | $(BLD_DIR)
	$(CC) $(CFLAGS) -w -c $< -o $@

# Removes outputs in the build directory
.PHONY: all clean
clean:
	rm -rf $(BLD_DIR)/*
