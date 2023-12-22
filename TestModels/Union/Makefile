# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.union
# TODO-Python: Move to smithy-build.json once Dafny SmithyBuildPlugin supports language-specific config
PYTHON_MODULE_NAME=simple_union

PROJECT_SERVICES := \
	SimpleUnion

SERVICE_NAMESPACE_SimpleUnion=simple.union

SERVICE_DEPS_SimpleUnion :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies
# DEPENDENT-MODELS:=
# LIBRARIES :=
transpile_net_dependencies:
