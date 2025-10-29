LAKE ?= lake

.PHONY: all run run-local lake

all: run run-local

# Link C binary against Lake package dynamic library

lake:
	$(LAKE) --dir=. build

PROJECT_ROOT = $(shell pwd)
OUT_DIR = out
LEAN_SYSROOT ?= $(shell lean --print-prefix)
LEAN_LIBDIR := $(LEAN_SYSROOT)/lib/lean

$(OUT_DIR):
	mkdir -p $@

build-local: $(OUT_DIR)/main-local
build: $(OUT_DIR)/main

ifneq ($(OS),Windows_NT)
# Add shared library paths to loader path (no Windows equivalent)
LINK_FLAGS=-Wl,-rpath,$(LEAN_LIBDIR) -Wl,-rpath,$(PWD)/.lake/build/lib
endif

$(OUT_DIR)/main: main.c lake | $(OUT_DIR)
# Add library paths for Lake package and for Lean itself
	cc -O3 -o $@ $< -I $(LEAN_SYSROOT)/include -L $(LEAN_LIBDIR) -L .lake/build/lib -lREPL -lInit_shared -lleanshared_1 -lleanshared $(LINK_FLAGS)

run: build
ifeq ($(OS),Windows_NT)
# Add shared library paths to loader path dynamically
	env PATH=".lake/build/lib:$(shell cygpath $(LEAN_SYSROOT))/bin:$(PATH)" $(OUT_DIR)/main
else
	$(OUT_DIR)/main
endif

# Alternatively, we can copy all shared lib dependencies to the current directory
# in order to avoid path set up and obtain a more portable executable

ifeq ($(OS),Windows_NT)
SHLIB_PREFIX :=
SHLIB_EXT := dll
LEAN_SHLIB_ROOT := $(shell cygpath $(LEAN_SYSROOT)/bin)
else
SHLIB_PREFIX := lib
# Add current directory to loader path (default on Windows)
ifeq ($(shell uname -s),Darwin)
LINK_FLAGS_LOCAL := -Wl,-rpath,@executable_path
SHLIB_EXT := dylib
else
LINK_FLAGS_LOCAL := -Wl,-rpath,'$${ORIGIN}'
SHLIB_EXT := so
endif
LEAN_SHLIB_ROOT := $(LEAN_LIBDIR)
endif

# 1. Compile process.c into an object
$(OUT_DIR)/process.o: process.c
	c++ -O3 -Wall -std=c++11 -fPIC  \
	    $(shell python3 -m pybind11 --includes) \
	    -I $(LEAN_SYSROOT)/include \
			$(LINK_FLAGS_LOCAL) \
	    -c $< -o $@

# 2. Link into Python extension
lean_process: $(OUT_DIR)/process.o
	c++ -undefined dynamic_lookup -shared \
	    $< \
			-L $(PROJECT_ROOT)/.lake/build/lib \
	    -L $(OUT_DIR) -lREPL -lInit_shared -lleanshared_1 -lleanshared -lSocket -lCli -lffi  \
	    -o $(OUT_DIR)/lean_process$(shell python3 -m pybind11 --extension-suffix)

$(OUT_DIR)/main-local: main.c lake | $(OUT_DIR)
	cp -f $(LEAN_SHLIB_ROOT)/*.$(SHLIB_EXT) .lake/build/lib/$(SHLIB_PREFIX)REPL.$(SHLIB_EXT) $(OUT_DIR)
	cc -O3 -o $@ $< -I $(LEAN_SYSROOT)/include -L $(PROJECT_ROOT)/.lake/build/lib -L $(OUT_DIR) -lREPL -lInit_shared -lleanshared_1 -lleanshared $(LINK_FLAGS_LOCAL)
	# c++ -O3 process.c -o $(OUT_DIR)/lean_process$(shell python3 -m pybind11 --extension-suffix) -undefined dynamic_lookup -Wall -shared -std=c++11 -fPIC $(shell python3 -m pybind11 --includes) -I $(LEAN_SYSROOT)/include -L $(OUT_DIR) -lREPL -lInit_shared -lleanshared_1 -lleanshared $(LINK_FLAGS_LOCAL)


run-local: build-local
	$(OUT_DIR)/main-local
