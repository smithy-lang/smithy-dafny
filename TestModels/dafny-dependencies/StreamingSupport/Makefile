
CORES=2

USE_DAFNY_STANDARD_LIBRARIES=1

include ../../SharedMakefile.mk

PYTHON_MODULE_NAME=smithy_dafny_streaming_support

transpile_java: | transpile_implementation_java transpile_test_java

transpile_python: | transpile_implementation_python transpile_test_python

# Overriding this target just to generate the project.properties file.
polymorph_dafny:
	cd $(CODEGEN_CLI_ROOT); \
	$(GRADLEW) run --args="\
	--library-root $(LIBRARY_ROOT) \
	--properties-file $(LIBRARY_ROOT)/project.properties \
	--model $(LIBRARY_ROOT)/Model \
	--namespace aws.polymorph \
	--dependent-model $(LIBRARY_ROOT)/../Model \
	";

_polymorph_dependencies: 
	echo "Skipping _polymorph_dependencies for StreamingSupport"