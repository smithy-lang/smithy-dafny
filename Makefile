# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

format_java_misc: setup_prettier
	npx prettier --plugin=prettier-plugin-java . --write

format_java_misc-check: setup_prettier
	npx prettier --plugin=prettier-plugin-java . --check

setup_prettier:
	npm i --no-save prettier@3 prettier-plugin-java@2.5

# Install packages via `python3 -m pip`,
# which is the syntax Smithy-Python and Smithy-Dafny Python use
# to invoke these packages.
# This helps ensure these packages are installed to the correct Python installation.
setup_smithy_dafny_python:
	python3 -m pip install docformatter black

setup_python: setup_smithy_dafny_python
setup_python:
	python3 -m pip install poetry

mvn_local_deploy_polymorph_dependencies: mvn_local_deploy_polymorph_rust_dependencies mvn_local_deploy_polymorph_python_dependencies

mvn_local_deploy_polymorph_rust_dependencies:
	cd smithy-dafny-codegen-modules/smithy-rs; \
	./gradlew :codegen-client:pTML :codegen-core:pTML :rust-runtime:pTML

mvn_local_deploy_polymorph_python_dependencies:
	cd codegen/smithy-dafny-codegen-modules/smithy-python/codegen; \
	./gradlew :smithy-python-codegen:pTML

mvn_local_deploy_polymorph:
	cd codegen; \
	./gradlew :smithy-dafny-codegen:pTML
