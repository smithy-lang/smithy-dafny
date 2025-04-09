module github.com/smithy-lang/smithy-dafny/ddb/test

go 1.23.0

replace github.com/smithy-lang/smithy-dafny/ddb v0.0.0 => ../ImplementationFromDafny-go
replace github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library => ../../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

require (
	github.com/aws/aws-sdk-go-v2/service/dynamodb v1.34.9
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.9.1
	github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library v0.0.0-00010101000000-000000000000
	github.com/smithy-lang/smithy-dafny/ddb v0.0.0
)

require (
	github.com/aws/aws-sdk-go-v2 v1.30.5 // indirect
	github.com/aws/aws-sdk-go-v2/config v1.27.33 // indirect
	github.com/aws/aws-sdk-go-v2/credentials v1.17.32 // indirect
	github.com/aws/aws-sdk-go-v2/feature/ec2/imds v1.16.13 // indirect
	github.com/aws/aws-sdk-go-v2/internal/configsources v1.3.17 // indirect
	github.com/aws/aws-sdk-go-v2/internal/endpoints/v2 v2.6.17 // indirect
	github.com/aws/aws-sdk-go-v2/internal/ini v1.8.1 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/accept-encoding v1.11.4 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/endpoint-discovery v1.9.18 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/presigned-url v1.11.19 // indirect
	github.com/aws/aws-sdk-go-v2/service/sso v1.22.7 // indirect
	github.com/aws/aws-sdk-go-v2/service/ssooidc v1.26.7 // indirect
	github.com/aws/aws-sdk-go-v2/service/sts v1.30.7 // indirect
	github.com/aws/smithy-go v1.20.4 // indirect
	github.com/jmespath/go-jmespath v0.4.0 // indirect
)
