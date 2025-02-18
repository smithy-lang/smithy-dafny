module github.com/smithy-lang/smithy-dafny/TestModels/Refinement/test

go 1.23.0

require github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library v0.0.0

require (
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.9.1
	github.com/smithy-lang/smithy-dafny/TestModels/Refinement v0.0.0-00010101000000-000000000000
)

replace github.com/smithy-lang/smithy-dafny/TestModels/Refinement => ../ImplementationFromDafny-go

replace github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/
