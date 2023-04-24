# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.dependencies

# This project takes dependencies on:
# - SimpleResource
# - SimpleExtendableResource
# - and SimpleConstraints modules.
DEPENDENT-MODELS:= \
	Resource \
	Extendable \
	Constraints
LIBRARIES := Resource \
	Extendable \
	Constraints

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
