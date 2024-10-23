# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1

include ../SharedMakefile.mk

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

PROJECT_SERVICES := \
	SQSExtended

MAIN_SERVICE_FOR_RUST := SQSExtended

# Dependencies external to this project
# Order is important
# In java they MUST be built
# in the order they depend on each other
PROJECT_DEPENDENCIES := \
	aws-sdks/sqs-via-cli

PROJECT_INDEX := \
	aws-sdks/sqs-via-cli/src/Index.dfy

SERVICE_NAMESPACE_SQSExtended=polymorph.tutorial.sqsextended

# Dependencies for each local service
SERVICE_DEPS_SQSExtended := \
	aws-sdks/sqs-via-cli

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

