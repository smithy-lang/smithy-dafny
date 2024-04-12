format_java_misc: setup_prettier
	npx prettier --plugin=prettier-plugin-java . --write

format_java_misc-check: setup_prettier
	npx prettier --plugin=prettier-plugin-java . --check

setup_prettier:
	npm i --no-save prettier@3 prettier-plugin-java@2.5
