# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

format_java_misc: setup_prettier
	npx prettier --plugin=prettier-plugin-java . --write

format_java_misc-check: setup_prettier
	npx prettier --plugin=prettier-plugin-java . --check

setup_prettier:
	npm i --no-save prettier@3 prettier-plugin-java@2.5

mvn_local_deploy_polymorph_dependencies:
	cd smithy-dafny-codegen-modules/smithy-rs; \
	./gradlew :codegen-client:pTML :codegen-core:pTML :rust-runtime:pTML

mvn_local_deploy_polymorph:
	cd codegen; \
	./gradlew :smithy-dafny-codegen:pTML
