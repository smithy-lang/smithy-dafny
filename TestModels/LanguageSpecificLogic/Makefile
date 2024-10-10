# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

RUST_BENERATED=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	LanguageSpecificLogic

MAIN_SERVICE_FOR_RUST := LanguageSpecificLogic

SERVICE_NAMESPACE_LanguageSpecificLogic=language.specific.logic

SERVICE_DEPS_LanguageSpecificLogic :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# Projects using replaceable modules must explicitly define these values.
NET_SRC_INDEX=src/replaces/net
NET_TEST_INDEX=test/replaces/net
PYTHON_SRC_INDEX=src/replaces/python
PYTHON_TEST_INDEX=test/replaces/python
RUST_SRC_INDEX=src/replaces/rust
RUST_TEST_INDEX=test/replaces/rust

RUST_OTHER_FILES=runtimes/rust/src/externs.rs

# This project has no dependencies 
# DEPENDENT-MODELS:=

# Python

PYTHON_MODULE_NAME=language_specific_logic

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../dafny-dependencies/StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr