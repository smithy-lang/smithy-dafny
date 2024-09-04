# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleAggregateReferences

SERVICE_NAMESPACE_SimpleAggregateReferences=simple.aggregate.references

SERVICE_DEPS_SimpleAggregateReferences :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

OUTPUT_DAFNY=--output-dafny $(LIBRARY_ROOT)/Model --include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy

GO_MODULE_NAME="github.com/smithy-lang/smithy-dafny/TestModels/AggregateReferences"

# Override wrapped target, since wrapping isn't supported for this module
_polymorph_wrapped :
	echo Skipping wrapped service for aggregate references

TRANSLATION_RECORD_GO := \
    dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/ImplementationFromDafny-go.dtr
# This project has no dependencies 
# DEPENDENT-MODELS:= 

