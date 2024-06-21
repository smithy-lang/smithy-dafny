# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=com.amazonaws.s3

PROJECT_SERVICES := \
    ComAmazonawsS3\

SERVICE_NAMESPACE_ComAmazonawsS3=com.amazonaws.s3

SERVICE_DEPS_ComAmazonawsS3 :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

AWS_SDK_CMD=--aws-sdk

# This project has no dependencies
# DEPENDENT-MODELS:=


SMITHY_MODEL_ROOT := $(LIBRARY_ROOT)/model

# Override calling the polymorph CLI to invoke the Smithy build instead
_polymorph_dafny:
	./gradlew polymorphDafny

_polymorph_dotnet:
	./gradlew polymorphDotnet


# There is no wrapped target for aws-sdk types
_polymorph_wrapped: ;
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;
_polymorph_wrapped_java: ;

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
