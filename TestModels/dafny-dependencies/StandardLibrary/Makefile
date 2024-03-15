# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

MAX_RESOURCE_COUNT=500000000

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

# Override SharedMakefile's transpile_net to not transpile
# StandardLibrary as a dependency
transpile_net: | transpile_implementation_net transpile_test_net

# Override SharedMakefile's transpile_java to not transpile
# StandardLibrary as a dependency
transpile_java: | transpile_implementation_java transpile_test_java

########################## Rust targets

transpile_rust: | _transpile_implementation_just_uint_rust _mv_implementation_rust

_transpile_implementation_just_uint_rust:
	find ./src -name 'UInt.dfy' | sed -e 's/^/include "/' -e 's/$$/"/' | dafny \
		-stdin \
		-noVerify \
		-vcsCores:$(CORES) \
		-compileTarget:rs \
		-spillTargetCode:3 \
		-compile:0 \
		-optimizeErasableDatatypeWrapper:0 \
		-compileSuffix:1 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out runtimes/rust/ImplementationFromDafny \

_mv_implementation_rust:
	rm -rf runtimes/rust/src
	mkdir -p runtimes/rust/src
	mv runtimes/rust/ImplementationFromDafny-rust/src/ImplementationFromDafny.rs runtimes/rust/src/lib.rs
	rm -rf runtimes/rust/ImplementationFromDafny-rust

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
		-compileSuffix:1 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-useRuntimeLib \
		-out $(OUT) \
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
