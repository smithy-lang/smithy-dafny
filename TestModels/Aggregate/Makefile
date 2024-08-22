# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1
RUST_BENERATED=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SimpleAggregate

SERVICE_NAMESPACE_SimpleAggregate=simple.aggregate

SERVICE_DEPS_SimpleAggregate :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/SimpleAggregateTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"simple.aggregate.internaldafny.types\" } SimpleAggregateTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module SimpleAggregateTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.aggregate.internaldafny\"} SimpleAggregate refines AbstractSimpleAggregateService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module SimpleAggregate refines AbstractSimpleAggregateService {"

WRAPPED_INDEX_FILE_PATH=src/WrappedSimpleAggregateImpl.dfy
WRAPPED_INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"simple.aggregate.internaldafny.wrapped\"} WrappedSimpleAggregateService refines WrappedAbstractSimpleAggregateService {"
WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING="module WrappedSimpleAggregateService refines WrappedAbstractSimpleAggregateService {"
