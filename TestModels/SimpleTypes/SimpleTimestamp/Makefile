# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=simple.types.timestamp

PROJECT_SERVICES := \
	SimpleTypesTimestamp

SERVICE_NAMESPACE_SimpleTypesTimestamp=simple.types.timestamp

SERVICE_DEPS_SimpleTypesTimestamp :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 


POLYMORPH_OPTIONS=--generate client-constructors,project-files

# Python

PYTHON_MODULE_NAME=simple_types_timestamp

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr