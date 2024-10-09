# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=com.amazonaws.lakeformation

PROJECT_SERVICES := \
	ComAmazonawsLakeformation\

SERVICE_NAMESPACE_ComAmazonawsLakeformation=com.amazonaws.lakeformation

SERVICE_DEPS_ComAmazonawsLakeformation :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

AWS_SDK_CMD=--aws-sdk

SMITHY_MODEL_ROOT := $(LIBRARY_ROOT)/model

# This project has no dependencies
# DEPENDENT-MODELS:=

POLYMORPH_OPTIONS=--generate project-files --generate client-constructors

# Override calling the polymorph CLI to invoke the Smithy build instead
_polymorph_dafny:
	$(GRADLEW) polymorphDafny

_polymorph_dotnet:
	$(GRADLEW) polymorphDotnet

_polymorph_java:
	$(GRADLEW) polymorphJava

# There is no wrapped target for aws-sdk types
_polymorph: ;
_polymorph_wrapped: ;
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;
_polymorph_wrapped_java: ;

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
