module github.com/smithy-lang/smithy-dafny/ddb

go 1.23.0

replace github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library => ../../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

require (
	github.com/aws/aws-sdk-go-v2/service/dynamodb v1.34.9
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.9.1
	github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library v0.0.0-00010101000000-000000000000
)

require (
	github.com/aws/aws-sdk-go-v2 v1.30.5 // indirect
	github.com/aws/aws-sdk-go-v2/internal/configsources v1.3.17 // indirect
	github.com/aws/aws-sdk-go-v2/internal/endpoints/v2 v2.6.17 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/accept-encoding v1.11.4 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/endpoint-discovery v1.9.18 // indirect
	github.com/aws/smithy-go v1.20.4 // indirect
	github.com/jmespath/go-jmespath v0.4.0 // indirect
)
