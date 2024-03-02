# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

PROJECT_ROOT := $(abspath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

SMITHY_DAFNY_ROOT := $(PROJECT_ROOT)/..
STD_LIBRARY := dafny-dependencies/StandardLibrary

include $(PROJECT_ROOT)/../SmithyDafnyMakefile.mk
