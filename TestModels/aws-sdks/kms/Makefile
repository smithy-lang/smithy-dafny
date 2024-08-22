# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

ENABLE_EXTERN_PROCESSING=1

include ../../SharedMakefile.mk

NAMESPACE=com.amazonaws.kms

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

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

# Constants for languages that drop extern names (Python, Go)

TYPES_FILE_PATH=Model/ComAmazonawsKmsTypes.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"software.amazon.cryptography.services.kms.internaldafny.types\" } ComAmazonawsKmsTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module ComAmazonawsKmsTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"software.amazon.cryptography.services.kms.internaldafny\"} Com.Amazonaws.Kms refines AbstractComAmazonawsKmsService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module Com.Amazonaws.Kms refines AbstractComAmazonawsKmsService {"
