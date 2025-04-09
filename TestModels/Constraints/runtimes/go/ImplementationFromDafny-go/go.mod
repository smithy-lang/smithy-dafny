module github.com/smithy-lang/smithy-dafny/TestModels/Constraints

go 1.23.0

require (
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.9.1
	github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library v0.0.0
)

replace github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/
