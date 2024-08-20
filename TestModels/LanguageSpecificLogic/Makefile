# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	LanguageSpecificLogic

SERVICE_NAMESPACE_LanguageSpecificLogic=language.specific.logic

SERVICE_DEPS_LanguageSpecificLogic :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# Projects using replaceable modules must explicitly define these values.
NET_SRC_INDEX=src/replaces/net
NET_TEST_INDEX=test/replaces/net

# This project has no dependencies 
# DEPENDENT-MODELS:= 

