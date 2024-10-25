# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# This evaluates to the local path _of this file_.
# This means that these are the project roots
# that are shared by all libraries in this repo.
PROJECT_ROOT := $(abspath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

SMITHY_DAFNY_ROOT := $(PROJECT_ROOT)/../..
STD_LIBRARY := ../../TestModels/dafny-dependencies/StandardLibrary

SMITHY_DEPS := ../../TestModels/dafny-dependencies/Model/traits.smithy

include $(SMITHY_DAFNY_ROOT)/SmithyDafnyMakefile.mk
