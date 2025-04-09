module github.com/smithy-lang/smithy-dafny/TestModels/Dependencies

go 1.23.0

require github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library v0.0.0

require github.com/smithy-lang/smithy-dafny/TestModels/Constraints v0.0.0

require github.com/smithy-lang/smithy-dafny/TestModels/Extendable v0.0.0

require github.com/smithy-lang/smithy-dafny/TestModels/Resource v0.0.0

require (
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.9.1
	github.com/smithy-lang/smithy-dafny/TestModels/Errors v0.0.0
)

replace github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

replace github.com/smithy-lang/smithy-dafny/TestModels/Constraints v0.0.0 => ../../../../Constraints/runtimes/go/ImplementationFromDafny-go

replace github.com/smithy-lang/smithy-dafny/TestModels/Extendable v0.0.0 => ../../../../Extendable/runtimes/go/ImplementationFromDafny-go

replace github.com/smithy-lang/smithy-dafny/TestModels/Resource v0.0.0 => ../../../../Resource/runtimes/go/ImplementationFromDafny-go

replace github.com/smithy-lang/smithy-dafny/TestModels/Errors v0.0.0 => ../../../../Errors/runtimes/go/ImplementationFromDafny-go
