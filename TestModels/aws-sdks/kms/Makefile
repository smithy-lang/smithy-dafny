# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

CORES=2

include ../../SharedMakefile.mk

PYTHON_MODULE_NAME=com_amazonaws_kms

PROJECT_SERVICES := \
	ComAmazonawsKms\

SERVICE_NAMESPACE_ComAmazonawsKms=com.amazonaws.kms

SERVICE_DEPS_ComAmazonawsKms :=

SMITHY_DEPS=dafny-dependencies/Model/traits.smithy

AWS_SDK_CMD=--aws-sdk

# This project has no dependencies
# DEPENDENT-MODELS:=
# LIBRARIES :=

# There is no wrapped target for aws-sdk types
_polymorph_wrapped: ;
_polymorph_wrapped_dafny: ;
_polymorph_wrapped_net: ;
_polymorph_wrapped_java: ;
polymorph_python: OUTPUT_PYTHON=--output-python $(LIBRARY_ROOT)/runtimes/python/smithygenerated
polymorph_python: _polymorph
polymorph_python:
	rm -rf runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated
	mkdir runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated
	mv runtimes/python/smithygenerated/$(PYTHON_MODULE_NAME)/* runtimes/python/src/$(PYTHON_MODULE_NAME)/smithygenerated
	rm -rf runtimes/python/smithygenerated
polymorph_python: POLYMORPH_LANGUAGE_TARGET=python
polymorph_python: _polymorph_dependencies

clean: _clean
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/dafny-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
	rm -rf $(LIBRARY_ROOT)/runtimes/java/src/test/dafny-generated
