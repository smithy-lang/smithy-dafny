
include ../SmithyDafnyMakefile.mk

PROJECT_ROOT := $(abspath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
SMITHY_DAFNY_ROOT := $(PROJECT_ROOT)
STD_LIBRARY := dafny-dependencies/StandardLibrary
