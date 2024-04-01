# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# This evaluates to the local path _of this file_.
# This means that these are the project roots
# that are shared by all libraries in this repo.
PROJECT_ROOT := $(abspath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

SMITHY_DAFNY_ROOT := $(PROJECT_ROOT)/..
STD_LIBRARY := dafny-dependencies/StandardLibrary

include $(SMITHY_DAFNY_ROOT)/SmithyDafnyMakefile.mk

# Override all the _polymorph_<LANG> targets to also build local service tests with _polymorph_wrapped,
# since all TestModels need to do that in place rather than in separate libraries.

_polymorph_code_gen: OUTPUT_DAFNY=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model)
_polymorph_code_gen: INPUT_DAFNY=\
		--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_code_gen: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_code_gen: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_code_gen: _polymorph
_polymorph_code_gen: OUTPUT_DAFNY_WRAPPED=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
		--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_code_gen: OUTPUT_DOTNET_WRAPPED=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped)
_polymorph_code_gen: _polymorph_wrapped

# Override this to make polymorph_dafny on the standard library,
# which generated the project.properties file.
polymorph_dafny: POLYMORPH_LANGUAGE_TARGET=dafny
polymorph_dafny: _polymorph_dependencies
polymorph_dafny:
	$(MAKE) -C $(PROJECT_ROOT)/$(STD_LIBRARY) polymorph_dafny
	set -e; for service in $(PROJECT_SERVICES) ; do \
		export service_deps_var=SERVICE_DEPS_$${service} ; \
		export namespace_var=SERVICE_NAMESPACE_$${service} ; \
		export SERVICE=$${service} ; \
		$(MAKE) _polymorph_dafny ; \
	done

_polymorph_dafny: OUTPUT_DAFNY=\
		--output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model)
_polymorph_dafny: INPUT_DAFNY=\
		--include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_dafny: _polymorph
_polymorph_dafny: OUTPUT_DAFNY_WRAPPED=\
    --output-dafny $(if $(DIR_STRUCTURE_V2), $(LIBRARY_ROOT)/dafny/$(SERVICE)/Model, $(LIBRARY_ROOT)/Model) \
    --include-dafny $(PROJECT_ROOT)/$(STD_LIBRARY)/src/Index.dfy
_polymorph_dafny: _polymorph_wrapped

_polymorph_java: OUTPUT_JAVA=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_java: _polymorph
_polymorph_java: OUTPUT_JAVA_WRAPPED=--output-java $(LIBRARY_ROOT)/runtimes/java/src/main/smithy-generated
_polymorph_java: _polymorph_wrapped

_polymorph_dotnet: OUTPUT_DOTNET=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/)
_polymorph_dotnet: _polymorph
_polymorph_dotnet: OUTPUT_DOTNET_WRAPPED=\
    $(if $(DIR_STRUCTURE_V2), --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped/$(SERVICE)/, --output-dotnet $(LIBRARY_ROOT)/runtimes/net/Generated/Wrapped)
_polymorph_dotnet: _polymorph_wrapped

_polymorph_python: OUTPUT_PYTHON=--output-python $(LIBRARY_ROOT)/runtimes/python/smithygenerated
_polymorph_python: MODULE_NAME=--module-name $(PYTHON_MODULE_NAME)
# Python codegen MUST know dependencies' module names...
# This greps each service dependency's Makefile for two strings:
# 1. "SERVICE_NAMESPACE_$(dependency)"
# 2. "PYTHON_MODULE_NAME"
# , then assembles them together as
# "SERVICE_NAMESPACE_$(dependency)"="PYTHON_MODULE_NAME"
# , creating a map from a service namespace to its wrapping module name.
# We plan to move this information into Dafny project files.
# This is unfortunately one long line that breaks when I split it up...
_polymorph_python: DEPENDENCY_MODULE_NAMES=$(foreach dependency, \
		$($(service_deps_var)), \
		--dependency-module-name=$(shell cat $(if $(DIR_STRUCTURE_V2),$(PROJECT_ROOT)/$(dependency)/../../Makefile,$(PROJECT_ROOT)/$(dependency)/Makefile) | grep ^SERVICE_NAMESPACE_$(if $(DIR_STRUCTURE_V2),$(shell echo $(dependency) | cut -d "/" -f 3),$(shell echo $($(dependency)))) | cut -d "=" -f 2)=$(shell cat $(if $(DIR_STRUCTURE_V2),$(PROJECT_ROOT)/$(dependency)/../../Makefile,$(PROJECT_ROOT)/$(dependency)/Makefile) | grep ^PYTHON_MODULE_NAME | cut -d "=" -f 2)\
	)
_polymorph_python: _polymorph
_polymorph_python: OUTPUT_PYTHON_WRAPPED=--output-python $(LIBRARY_ROOT)/runtimes/python/smithygenerated
_polymorph_python: _polymorph_wrapped
_polymorph_python: POLYMORPH_LANGUAGE_TARGET=python
_polymorph_python: _polymorph_dependencies