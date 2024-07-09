# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# For this project, the Makefile should ONLY be used for:
# - make transpile_net
# - make test_net
# The polymorph commands should be done using gradle instead. 

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=com.amazonaws.sqs

PROJECT_SERVICES := \
	ComAmazonawsSqs \

SERVICE_NAMESPACE_ComAmazonawsSqs=com.amazonaws.sqs

SERVICE_DEPS_ComAmazonawsSqs :=

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
_polymorph: ;
_polymorph_wrapped: ;
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;
_polymorph_wrapped_java: ;
