
CORES=2

USES_STREAMING=1

include ../../SharedMakefile.mk

PYTHON_MODULE_NAME=smithy_dafny_streaming_support

TRANSLATION_RECORD_PYTHON := \
    --translation-record ../StandardLibrary/runtimes/python/src/smithy_dafny_standard_library/internaldafny/generated/dafny_src-py.dtr


transpile_java: | transpile_implementation_java transpile_test_java

transpile_python: | transpile_implementation_python transpile_test_python

# Overriding this target just to generate the project.properties file.
polymorph_dafny: build_dafny_stdlibs
	cd $(CODEGEN_CLI_ROOT); \
	$(GRADLEW) run --args="\
	--library-root $(LIBRARY_ROOT) \
	--properties-file $(LIBRARY_ROOT)/project.properties \
	--model $(LIBRARY_ROOT)/Model \
	--namespace aws.polymorph \
	--dependent-model $(LIBRARY_ROOT)/../Model \
	";

build_dafny_stdlibs:
	dafny build -t:lib --output bin/DafnyStandardLibraries-smithy-dafny-subset.doo DafnyStandardLibraries-smithy-dafny-subset.toml
	rm -rf DafnyStandardLibraries-smithy-dafny-subset-lib

_polymorph_dependencies: 
	echo "Skipping _polymorph_dependencies for StreamingSupport"