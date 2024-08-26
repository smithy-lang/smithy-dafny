# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# These are make targets that use sed to replace extern names.
# Some Smithy-Dafny modules declare extern attributes with names that do not work in all languages.
# These targets can remove or add those extern names based on the target language.
# A target language SHOULD declare use of these targets.

# These should eventually be replaced by replaceable modules that declare per-language extern names.
# See https://github.com/smithy-lang/smithy-dafny/issues/528.
# Eventually, the replaceable modules should be removed (or, their extern names should be removed),
# and should be replaced by per-language package/namespace prefixes.

# On macOS, sed requires an extra parameter of ""
OS := $(shell uname)
ifeq ($(OS), Darwin)
  SED_PARAMETER := ""
else
  SED_PARAMETER :=
endif

# Before transpiling to a target language that does not expect externs,
# remove any extern attributes.
_no_extern_pre_transpile: _no_extern_pre_transpile_dependencies _sed_types_file_remove_extern _sed_index_file_remove_extern _sed_wrapped_types_file_remove_extern
# After transpiling to a target language that does not expect externs,
# then add back any extern attributes,
# because the expected committed state has extern attributes.
_no_extern_post_transpile: _no_extern_post_transpile_dependencies _sed_types_file_add_extern _sed_index_file_add_extern _sed_wrapped_types_file_add_extern
# Before transpiling to a target language that does expect externs,
# add back any extern attributes if they are not present.
_with_extern_pre_transpile: _with_extern_pre_transpile_dependencies _sed_types_file_add_extern _sed_index_file_add_extern _sed_wrapped_types_file_add_extern
# After transpiling to a target language that does expect externs,
# add back any extern attributes if they are not present for any reason.
_with_extern_post_transpile: _with_extern_post_transpile_dependencies _sed_types_file_add_extern _sed_index_file_add_extern _sed_wrapped_types_file_add_extern

_no_extern_pre_transpile_dependencies:
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% _no_extern_pre_transpile;, $(PROJECT_DEPENDENCIES))

_no_extern_post_transpile_dependencies:
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% _no_extern_post_transpile;, $(PROJECT_DEPENDENCIES))

_with_extern_pre_transpile_dependencies:
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% _with_extern_pre_transpile;, $(PROJECT_DEPENDENCIES))

_with_extern_post_transpile_dependencies:
	$(patsubst %, $(MAKE) -C $(PROJECT_ROOT)/% _with_extern_post_transpile;, $(PROJECT_DEPENDENCIES))

_sed_types_file_remove_extern:
	@if [ -z $(TYPES_FILE_PATH) ] || [ -z $(TYPES_FILE_WITH_EXTERN_STRING) ] || [ -z $(TYPES_FILE_WITHOUT_EXTERN_STRING) ]; then \
		echo "Error: All variables TYPES_FILE_PATH, TYPES_FILE_WITH_EXTERN_STRING, and TYPES_FILE_WITHOUT_EXTERN_STRING must be set and non-empty."; \
		exit 1; \
	fi
	$(MAKE) _sed_file SED_FILE_PATH=$(TYPES_FILE_PATH) SED_BEFORE_STRING=$(TYPES_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(TYPES_FILE_WITHOUT_EXTERN_STRING)

_sed_index_file_remove_extern:
	@if [ -z $(INDEX_FILE_PATH) ] || [ -z $(INDEX_FILE_WITH_EXTERN_STRING) ] || [ -z $(INDEX_FILE_WITHOUT_EXTERN_STRING) ]; then \
		echo "Error: All variables INDEX_FILE_PATH, INDEX_FILE_WITH_EXTERN_STRING, and INDEX_FILE_WITHOUT_EXTERN_STRING must be set and non-empty."; \
		exit 1; \
	fi
	$(MAKE) _sed_file SED_FILE_PATH=$(INDEX_FILE_PATH) SED_BEFORE_STRING=$(INDEX_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(INDEX_FILE_WITHOUT_EXTERN_STRING)

_sed_wrapped_types_file_remove_extern:
	$(if $(strip $(WRAPPED_INDEX_FILE_PATH)), $(MAKE) _sed_file SED_FILE_PATH=$(WRAPPED_INDEX_FILE_PATH) SED_BEFORE_STRING=$(WRAPPED_INDEX_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING), )

_sed_types_file_add_extern:
	@if [ -z $(TYPES_FILE_PATH) ] || [ -z $(TYPES_FILE_WITH_EXTERN_STRING) ] || [ -z $(TYPES_FILE_WITHOUT_EXTERN_STRING) ]; then \
		echo "Error: All variables TYPES_FILE_PATH, TYPES_FILE_WITH_EXTERN_STRING, and TYPES_FILE_WITHOUT_EXTERN_STRING must be set and non-empty."; \
		exit 1; \
	fi
	$(MAKE) _sed_file SED_FILE_PATH=$(TYPES_FILE_PATH) SED_BEFORE_STRING=$(TYPES_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(TYPES_FILE_WITH_EXTERN_STRING)

_sed_index_file_add_extern:
	@if [ -z $(INDEX_FILE_PATH) ] || [ -z $(INDEX_FILE_WITH_EXTERN_STRING) ] || [ -z $(INDEX_FILE_WITHOUT_EXTERN_STRING) ]; then \
		echo "Error: All variables INDEX_FILE_PATH, INDEX_FILE_WITH_EXTERN_STRING, and INDEX_FILE_WITHOUT_EXTERN_STRING must be set and non-empty."; \
		exit 1; \
	fi
	$(MAKE) _sed_file SED_FILE_PATH=$(INDEX_FILE_PATH) SED_BEFORE_STRING=$(INDEX_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(INDEX_FILE_WITH_EXTERN_STRING)

_sed_wrapped_types_file_add_extern:
	$(if $(strip $(WRAPPED_INDEX_FILE_PATH)), $(MAKE) _sed_file SED_FILE_PATH=$(WRAPPED_INDEX_FILE_PATH) SED_BEFORE_STRING=$(WRAPPED_INDEX_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(WRAPPED_INDEX_FILE_WITH_EXTERN_STRING), )

_sed_file:
	bash $(SMITHY_DAFNY_ROOT)/scripts/sed_replace.sh
