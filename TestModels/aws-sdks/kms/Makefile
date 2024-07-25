# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

PROJECT_SERVICES := \
	ComAmazonawsKms\

SERVICE_NAMESPACE_ComAmazonawsKms=com.amazonaws.kms

SERVICE_DEPS_ComAmazonawsKms :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

AWS_SDK_CMD=--aws-sdk

# This project has no dependencies
# DEPENDENT-MODELS:=


# There is no wrapped target for aws-sdk types
_polymorph_wrapped: ;
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;
_polymorph_wrapped_java: ;
_polymorph_wrapped_python: ;

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

# Python

PYTHON_MODULE_NAME=com_amazonaws_kms

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../../dafny-dependencies/StandardLibrary/runtimes/python/src/standard_library/internaldafny/generated/dafny_src-py.dtr
