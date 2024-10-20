# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=1

include ../SharedMakefile.mk

PROJECT_SERVICES := \
	SQSExtendedClient

MAIN_SERVICE_FOR_RUST := SQSExtendedClient

# Dependencies external to this project
# Order is important
# In java they MUST be built
# in the order they depend on each other
PROJECT_DEPENDENCIES := \
	SQS

PROJECT_INDEX := \
	SQS/src/Index.dfy

SERVICE_NAMESPACE_SQSExtendedClient=com.amazonaws.sqsextended

# Dependencies for each local service
SERVICE_DEPS_SQSExtendedClient := \
	SQS

POLYMORPH_OPTIONS=--generate project-files

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated

