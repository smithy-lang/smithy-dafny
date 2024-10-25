# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

TRANSPILE_TESTS_IN_RUST=true

include ../../SharedMakefile.mk

MAX_RESOURCE_COUNT=500000000
PYTHON_MODULE_NAME=smithy_dafny_standard_library
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
	--library-root $(LIBRARY_ROOT) \
	--properties-file $(PROJECT_ROOT)/$(STD_LIBRARY)/project.properties \
	--model $(PROJECT_ROOT)/$(STD_LIBRARY)/Model \
	--namespace aws.polymorph \
	--dependent-model $(PROJECT_ROOT)/$(STD_LIBRARY)/../Model \
	";

polymorph_dotnet:
	echo "Skipping polymorph_dotnet for StandardLibrary"

polymorph_java:
	echo "Skipping polymorph_java for StandardLibrary"

polymorph_python:
	echo "Skipping polymorph_python for StandardLibrary"

polymorph_rust:
	echo "Skipping polymorph_rust for StandardLibrary"

patch_after_transpile_rust:
	echo "Skipping patch_after_transpile_rust for StandardLibrary"

_polymorph_dependencies: 
	echo "Skipping _polymorph_dependencies for StandardLibrary"

# Override SharedMakefile's transpile_net to not transpile
# StandardLibrary as a dependency
transpile_net: | transpile_implementation_net transpile_test_net

# Override SharedMakefile's transpile_java to not transpile
# StandardLibrary as a dependency
transpile_java: | transpile_implementation_java transpile_test_java

# Override SharedMakefile's transpile_python to not transpile
# StandardLibrary as a dependency
transpile_python: | transpile_implementation_python transpile_test_python

########################## Rust targets
# Override SharedMakefile's transpile_java to not transpile
# StandardLibrary as a dependency
transpile_rust: | transpile_implementation_rust

RUST_OTHER_FILES=runtimes/rust/src/conversion.rs runtimes/rust/src/UTF8_externs.rs

# These are necessary just for the patch_after_transpile_rust target
MAIN_SERVICE_FOR_RUST := StandardLibrary
SERVICE_NAMESPACE_StandardLibrary=aws.polymorph
SERVICE_DEPS_StandardLibrary :=
SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

# Override this target to not insert a dependency on the standard library.
_mv_implementation_rust:
	mv implementation_from_dafny-rust/src/implementation_from_dafny.rs runtimes/rust/src/implementation_from_dafny.rs
	rustfmt runtimes/rust/src/implementation_from_dafny.rs
	rm -rf implementation_from_dafny-rust

transpile_dependencies:
	echo "Skipping transpile_dependencies for StandardLibrary"

# Override SharedMakefile's transpile_implementation to not reference
# StandardLibrary as a Library
transpile_implementation: SRC_INDEX_TRANSPILE=$(if $(SRC_INDEX),$(SRC_INDEX),src)
transpile_implementation:
	find ./dafny/**/$(SRC_INDEX_TRANSPILE)/ ./$(SRC_INDEX_TRANSPILE)/ -name 'Index.dfy' | sed -e 's/^/include "/' -e 's/$$/"/' | dafny \
	translate $(TARGET) \
		--stdin \
		--no-verify \
		--cores:$(CORES) \
		--optimize-erasable-datatype-wrapper:false \
		--unicode-char:false \
		--function-syntax:3 \
		--output $(OUT) \
		$(DAFNY_OPTIONS) \
		$(DAFNY_OTHER_FILES) \
		$(TRANSPILE_MODULE_NAME)

# Override SharedMakefile's build_java to not install
# StandardLibrary as a dependency
build_java: transpile_java
	gradle -p runtimes/java build

# Override SharedMakefile's mvn_local_deploy to
# issue warning
mvn_local_deploy:
	@echo "${RED}Warning!!${YELLOW} Installing TestModel's STD to Maven Local replaces ESDK's STD!\n$(RESET)" >&2
	gradle -p runtimes/java publishToMavenLocal

dafny_benerate: DAFNY_RUST_OUTPUT=\
	runtimes/rust/implementation_from_dafny
dafny_benerate: DAFNY_RUST_OUTPUT_FOLDER=\
	$(DAFNY_RUST_OUTPUT)-rust/src
dafny_benerate: DAFNY_RUST_OUTPUT_RS=\
	$(DAFNY_RUST_OUTPUT_FOLDER)/implementation_from_dafny.rs
dafny_benerate: DAFNY_RUST_OUTPUT_RS_DTR=\
	$(DAFNY_RUST_OUTPUT_FOLDER)/implementation_from_dafny-rs.dtr
dafny_benerate: DAFNY_RUST_IMPL=\
	runtimes/rust/src/implementation_from_dafny.rs
dafny_benerate:
	$(DAFNY) translate rs src/Index.dfy  --emit-uncompilable-code --no-verify   --optimize-erasable-datatype-wrapper false   --include-runtime   --compile-suffix true   --unicode-char false   --function-syntax 3   --allow-warnings   --output $(DAFNY_RUST_OUTPUT)
	rustfmt $(DAFNY_RUST_OUTPUT_RS)
	# echo "Diffs remaining till code generation works:"
	# diff -u $(DAFNY_RUST_OUTPUT_RS) $(DAFNY_RUST_IMPL) | wc -l
	mv $(DAFNY_RUST_OUTPUT_RS) $(DAFNY_RUST_IMPL)
	rm $(DAFNY_RUST_OUTPUT_RS_DTR);
	rm -r $(DAFNY_RUST_OUTPUT_FOLDER);
