module github.com/smithy-lang/smithy-dafny/TestModels/Resource/test

go 1.23.0

require github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library v0.0.0

require (
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.9.1
	github.com/smithy-lang/smithy-dafny/TestModels/Resource v0.0.0
)

replace github.com/smithy-lang/smithy-dafny/TestModels/Resource v0.0.0 => ../ImplementationFromDafny-go

//TODO: Drop this after Dafny fixes the https://t.corp.amazon.com/P150784381
replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../DafnyRuntimeGo/

replace github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/
