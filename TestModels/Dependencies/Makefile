# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.dependencies
# TODO-Python: Move to smithy-build.json once Dafny SmithyBuildPlugin supports language-specific config
PYTHON_MODULE_NAME=simple_dependencies

# This project takes dependencies on:
# - SimpleResource
# - SimpleErrors
# - SimpleExtendableResource
# - and SimpleConstraints modules.
DEPENDENT-MODELS:= \
	Resource \
	Errors \
	Extendable \
	Constraints
LIBRARIES := Resource \
	Errors \
	Extendable \
	Constraints

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
