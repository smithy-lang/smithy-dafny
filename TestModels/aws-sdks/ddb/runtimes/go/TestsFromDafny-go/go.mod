module github.com/smithy-lang/smithy-dafny/ddb/test

go 1.23.0

replace github.com/smithy-lang/smithy-dafny/ddb v0.0.0 => ../ImplementationFromDafny-go

replace github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library => ../../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/
