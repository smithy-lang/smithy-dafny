# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

NAMESPACE=simple.types.smithyString

PROJECT_SERVICES := \
	SimpleString

SERVICE_NAMESPACE_SimpleString=simple.types.smithyString

SERVICE_DEPS_SimpleString :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# This project has no dependencies 
# DEPENDENT-MODELS:= 

########################## Rust targets

# Starting to add makefile targets for Rust, but only in individial libraries for now
# since Rust support in Dafny is not yet complete.
# But we want to lock down what IS working to ensure we don't have regressions
# and gradually expand the scope of what we're testing.

# This library's runtimes/rust folder is entirely hand-generated at the moment,
# just showing the intended target that combines what smithy-rs already generates
# with what we want polymorph_rust to generate.

build_rust:
	cd runtimes/rust; \
	cargo build

test_rust:
	cd runtimes/rust; \
	cargo test

##########################