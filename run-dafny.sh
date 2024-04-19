dafny \
		-vcsCores:$1 \
		-compile:0 \
		-definiteAssignment:3 \
		-unicodeChar:0 \
		-functionSyntax:3 \
		-verificationLogger:csv \
		-timeLimit:$2 \
		-trace \
		$3
echo "$3 has exit code $?"
