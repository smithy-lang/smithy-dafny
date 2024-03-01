# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

PROJECT_ROOT := $(abspath $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# This finds all Dafny projects in this repository
# This makes building root level targets for each project easy
PROJECTS = $(shell  find . -mindepth 2 -maxdepth 2 -type f -name "Makefile" | xargs dirname | xargs basename)

verify:
	$(foreach PROJECT, $(PROJECTS), \
		$(MAKE) -C $(PROJECT) verify CORES=4 && \
	) true

dafny-reportgenerator:
	$(foreach PROJECT, $(PROJECTS), \
		$(MAKE) -C $(PROJECT) dafny-reportgenerator && \
	) true

clean-dafny-report:
	$(foreach PROJECT, $(PROJECTS), \
		$(MAKE) -C $(PROJECT) clean-dafny-report && \
	) true

format_dafny:
	$(foreach PROJECT, $(PROJECTS), \
		$(MAKE) -C $(PROJECT) format_dafny && \
	) true

format_net:
	$(foreach PROJECT, $(PROJECTS), \
		$(MAKE) -C $(PROJECT) format_net && \
	) true

format_java_misc:
	npx prettier --plugin=prettier-plugin-java . --write

format_java_misc-check:
	npx prettier --plugin=prettier-plugin-java . --check

setup_prettier:
	npm i --no-save prettier@3 prettier-plugin-java@2.5

polymorph_code_gen:
	$(foreach PROJECT, $(PROJECTS), \
		$(MAKE) -C $(PROJECT) polymorph_code_gen && \
	) true

setup_semantic_release:
	npm i --no-save semantic-release @semantic-release/changelog semantic-release-replace-plugin @semantic-release/git

run_semantic_release:
	npx semantic-release --no-ci

dry_run_semantic_release:
	npx semantic-release --dry-run

duvet: | duvet_extract duvet_report

duvet_extract:
	rm -rf compliance
	$(foreach file, $(shell find aws-encryption-sdk-specification/framework -name '*.md'), duvet extract -o compliance -f MARKDOWN $(file);)
	# $(foreach file, $(shell find aws-encryption-sdk-specification/client-apis -name '*.md'), duvet extract -o compliance -f MARKDOWN $(file);)
	# $(foreach file, $(shell find aws-encryption-sdk-specification/data-format -name '*.md'), duvet extract -o compliance -f MARKDOWN $(file);)

duvet_report:
	duvet \
		report \
		--spec-pattern "compliance/**/*.toml" \
		--source-pattern "AwsCryptographicMaterialProviders/dafny/**/src/**/*.dfy" \
		--source-pattern "AwsCryptographicMaterialProviders/dafny/**/test/**/*.dfy" \
		--source-pattern "AwsCryptographicMaterialProviders/dafny/**/Model/**/*.smithy" \
		--source-pattern "AwsCryptographicMaterialProviders/compliance_exceptions/**/*.txt" \
		--source-pattern "TestVectorsAwsCryptographicMaterialProviders/compliance_exceptions/**/*.txt" \
		--source-pattern "(# //=,# //#).github/workflows/duvet.yaml" \
		--source-pattern "TestVectorsAwsCryptographicMaterialProviders/dafny/**/src/**/*.dfy" \
		--html specification_compliance_report.html

# Generate the top-level project.properties file using smithy-dafny.
# This is for the benefit of the nightly Dafny CI,
# to verify that everything works with the latest Dafny prerelease.
# We use smithy-dafny rather than just cat-ing the file directly
# because smithy-dafny currently maintains the knowledge
# of how Dafny release versions maps to Dafny runtime library versions,
# especially prerelease versions like 4.4.0-nightly-2024-01-30-908f95f.
generate_properties_file: 
	cd smithy-dafny/codegen/smithy-dafny-codegen-cli; \
	./../gradlew run --args="\
	--dafny-version ${DAFNY_VERSION} \
	--library-root $(PROJECT_ROOT)/StandardLibrary \
	--model $(PROJECT_ROOT)/StandardLibrary/Model \
	--dependent-model $(PROJECT_ROOT)/StandardLibrary/Model \
	--namespace aws.polymorph \
	--properties-file $(PROJECT_ROOT)/project.properties \
	";
