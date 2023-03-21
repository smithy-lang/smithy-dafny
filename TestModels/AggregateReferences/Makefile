# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.aggregate.references
OUTPUT_DAFNY=--output-dafny $(LIBRARY_ROOT)/Model --include-dafny $(STANDARD_LIBRARY_PATH)/src/Index.dfy

# Override wrapped target, since wrapping isn't supported for this module
_polymorph_wrapped :
	echo Skipping wrapped service for aggregate references

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=
