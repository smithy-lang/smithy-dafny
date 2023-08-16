# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

MAX_RESOURCE_COUNT=500000000
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

polymorph_dafny :
	echo "Skipping polymorph_dafny for StandardLibrary"

polymorph_net :
	echo "Skipping polymorph_net for StandardLibrary"

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
	find src -regex ".*\.dfy" -type f -exec sed -i $(SED) '/module {:extern \".*\"/s/\./_/g' {} \;
	echo "Skipping Model modification for StandardLibrary"
	find test -regex ".*\.dfy" -type f -exec sed -i $(SED) '/module {:extern \".*\"/s/\./_/g' {} \;

_python_revert_underscore_extern_names:
	find src -regex ".*\.dfy" -type f -exec sed -i $(SED) '/module {:extern \".*\"/s/_/\./g' {} \;
	echo "Skipping Model modification for StandardLibrary"
	find test -regex ".*\.dfy" -type f -exec sed -i $(SED) '/module {:extern \".*\"/s/_/\./g' {} \;

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
		$(COMPILE_SUFFIX_OPTION) \
		-quantifierSyntax:3 \
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
