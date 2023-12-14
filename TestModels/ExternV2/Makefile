# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../SharedMakefile.mk

NAMESPACE=simple.dafnyExternV2

DOT_NAMESPACE_SRC_INDEX=src/IndexDotNamespaced.dfy
UNDERSCORE_NAMESPACE_SRC_INDEX=src/IndexUnderscoreNamespaced.dfy

# For this example, the `src` modules have language-specific behavior,
# so they cannot share src Index files.
NET_SRC_INDEX=src/IndexNet.dfy
JAVA_SRC_INDEX=src/IndexJava.dfy

DOT_NAMESPACE_TEST_INDEX=test/WrappedTestDotNamespaced.dfy
UNDERSCORE_NAMESPACE_TEST_INDEX=test/WrappedTestUnderscoreNamespaced.dfy

# For this examples, the `test` modules do not have language-specific behavior,
# so a language-specific Index file is not needed.
# If language-specific behavior is added, this would need to be changed.
JAVA_TEST_INDEX=$(DOT_NAMESPACE_TEST_INDEX)

# This project MUST be transpiled with V2
transpile_implementation: | transpile_implementation_v2
	exit 0

transpile_test: | transpile_test_v2
	exit 0

transpile_dependencies: | transpile_dependencies_v2
	exit 0

transpile_net: | transpile_net_v2
	exit 0

# This project has no dependencies 
# DEPENDENT-MODELS:= 
# LIBRARIES :=
