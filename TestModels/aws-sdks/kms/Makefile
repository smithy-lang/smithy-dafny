# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

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
