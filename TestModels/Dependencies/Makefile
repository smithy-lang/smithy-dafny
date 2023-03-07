# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.dependencies

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