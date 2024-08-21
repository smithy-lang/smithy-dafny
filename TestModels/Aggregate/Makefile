# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

RUST_BENERATED=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleAggregate

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr

SERVICE_NAMESPACE_SimpleAggregate=simple.aggregate

SERVICE_DEPS_SimpleAggregate :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# Python

PYTHON_MODULE_NAME=simple_aggregate

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr