# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# For this project, the Makefile should ONLY be used for:
# - make transpile_net
# - make test_net
# The polymorph commands should be done using gradle instead. 

CORES=2

TRANSPILE_TESTS_IN_RUST=1

include ../../SharedMakefile.mk


PROJECT_SERVICES := \
	ComAmazonawsDynamodb

MAIN_SERVICE_FOR_RUST := ComAmazonawsDynamodb

SERVICE_NAMESPACE_ComAmazonawsDynamodb=com.amazonaws.dynamodb

SERVICE_DEPS_ComAmazonawsDynamodb :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

AWS_SDK_CMD=--aws-sdk

# This project has no dependencies
# DEPENDENT-MODELS:=


SMITHY_MODEL_ROOT := $(LIBRARY_ROOT)/model

# Override calling the polymorph CLI to invoke the Smithy build instead
_polymorph_dafny:
	$(GRADLEW) polymorphDafny

_polymorph_dotnet:
	$(GRADLEW) polymorphDotnet

_polymorph_java:
	$(GRADLEW) polymorphJava

_polymorph_rust:
	$(GRADLEW) polymorphRust

# There is no wrapped target for aws-sdk types
_polymorph: ;
_polymorph_wrapped: ;
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;
_polymorph_wrapped_java: ;

