# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

MAX_RESOURCE_COUNT=500000000
# TODO-Python-PYTHONPATH: Move into dfyproject.toml
PYTHON_MODULE_NAME=standard_library
LIBRARIES :=

# define standard colors
ifneq (,$(findstring xterm,${TERM}))
	RED          := $(shell tput -Txterm setaf 1)
	YELLOW       := $(shell tput -Txterm setaf 3)
	RESET := $(shell tput -Txterm sgr0)
else
	RED          := ""
	YELLOW       := ""
	RESET        := ""
endif

# Overriding this target just to generate the project.properties file
polymorph_dafny :
	cd $(CODEGEN_CLI_ROOT); \
	$(GRADLEW) run --args="\
	--dafny-version $(DAFNY_VERSION) \
	--library-root $(LIBRARY_ROOT) \
	--properties-file $(PROJECT_ROOT)/$(STD_LIBRARY)/project.properties \
	--model $(PROJECT_ROOT)/$(STD_LIBRARY)/Model \
	--namespace aws.polymorph \
	--dependent-model $(PROJECT_ROOT)/$(STD_LIBRARY)/../Model \
	";

polymorph_dotnet :
	echo "Skipping polymorph_dotnet for StandardLibrary"

polymorph_java :
	echo "Skipping polymorph_java for StandardLibrary"

polymorph_python :
	echo "Skipping polymorph_python for StandardLibrary"

# Override SharedMakefile's transpile_net to not transpile
# StandardLibrary as a dependency
transpile_net: | transpile_implementation_net transpile_test_net

# Override SharedMakefile's transpile_java to not transpile
# StandardLibrary as a dependency
transpile_java: | transpile_implementation_java transpile_test_java

# Override SharedMakefile's transpile_python to not transpile
# StandardLibrary as a dependency
transpile_python: | transpile_implementation_python transpile_test_python

# Hacky workaround until Dafny supports per-language extern names.
# Replaces `.`s with `_`s in strings like `{:extern ".*"}`.
# This is flawed logic and should be removed, but is a reasonable band-aid for now.
# TODO: Once Dafny supports per-language extern names, remove and replace with Pythonic extern names.
# This may require new Smithy-Dafny logic to generate Pythonic extern names.
_python_underscore_extern_names:
	find src -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/module {:extern \".*\"/s/\./_/g' {} \;
	echo "Skipping Model modification for StandardLibrary"
	find test -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/module {:extern \".*\"/s/\./_/g' {} \;

_python_revert_underscore_extern_names:
	find src -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/module {:extern \".*\"/s/_/\./g' {} \;
	echo "Skipping Model modification for StandardLibrary"
	find test -regex ".*\.dfy" -type f -exec sed -i $(SED_PARAMETER) '/module {:extern \".*\"/s/_/\./g' {} \;

########################## Rust targets

# Starting to add makefile targets for Rust, but only in this library for now
# since Rust support in Dafny is not yet complete.
# But we want to lock down what IS working to ensure we don't have regressions
# and gradually expand the scope of what we're testing.

# TODO:
#  1. Only building UInt.dfy to start because other files use unsupported features
#     (e.g. the variance specifiers in Option<+T>).
#     This scope should be expanded over time.
#  2. Using -compile:1 instead of -compile:0 because the Rust backend incorrectly
#     only outputs the runtime source when compiling the target program.
#     See https://github.com/dafny-lang/dafny/issues/5203.
#  3. Unlike other backends, the Rust backend emits full Rust projects,
#     including Cargo.toml.
#     This runs contrary to the smithy-dafny philosophy
#     of translating code into predefined projects
#     and combining it with smithy-generated and hand-written code.
#     We'll need some Dafny-side design discussion to support both use cases.

transpile_rust: | _transpile_implementation_just_uint_rust _mv_implementation_rust

_transpile_implementation_just_uint_rust:
	find ./src -name 'UInt.dfy' | sed -e 's/^/include "/' -e 's/$$/"/' | dafny \
		-stdin \
		-noVerify \
		-vcsCores:$(CORES) \
		-compileTarget:rs \
		-spillTargetCode:3 \
		-compile:1 \
		-optimizeErasableDatatypeWrapper:0 \
		-compileSuffix:1 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-out ImplementationFromDafny \

_mv_implementation_rust:
	rm -rf runtimes/rust
	mv ImplementationFromDafny-rust runtimes/rust

build_rust: transpile_rust
	cd runtimes/rust; \
	cargo build

##########################

transpile_dependencies:
	echo "Skipping transpile_dependencies for StandardLibrary"

# Override SharedMakefile's transpile_implementation to not reference
# StandardLibrary as a Library
transpile_implementation:
	dafny \
		-vcsCores:$(CORES) \
		-compileTarget:$(TARGET) \
		-spillTargetCode:3 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-compileSuffix:0 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out $(OUT) \
		./src/Index.dfy

build_implementation:
	dafny build \
		-t:$(TARGET) \
		./src/Index.dfy \
		-o $(OUT) \
		--quantifier-syntax:3 \
		--function-syntax:3 \
		--optimize-erasable-datatype-wrapper:false \
		./src/Index.dfy

# Override SharedMakefile's build_java to not install
# StandardLibrary as a dependency
build_java: transpile_java
	gradle -p runtimes/java build

# Override SharedMakefile's mvn_local_deploy to
# issue warning
mvn_local_deploy:
	@echo "${RED}Warning!!${YELLOW} Installing TestModel's STD to Maven Local replaces ESDK's STD!\n$(RESET)" >&2
	gradle -p runtimes/java publishToMavenLocal
