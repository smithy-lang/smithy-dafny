module github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService

go 1.23.0

require (
	github.com/aws/smithy-go v1.22.0
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.9.1
	github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library v0.0.0
	github.com/smithy-lang/smithy-dafny/ddbv2 v0.0.0
	github.com/smithy-lang/smithy-dafny/kmsv2 v0.0.0
)

require (
	github.com/aws/aws-sdk-go-v2 v1.32.4 // indirect
	github.com/aws/aws-sdk-go-v2/config v1.28.3 // indirect
	github.com/aws/aws-sdk-go-v2/credentials v1.17.44 // indirect
	github.com/aws/aws-sdk-go-v2/feature/ec2/imds v1.16.19 // indirect
	github.com/aws/aws-sdk-go-v2/internal/configsources v1.3.23 // indirect
	github.com/aws/aws-sdk-go-v2/internal/endpoints/v2 v2.6.23 // indirect
	github.com/aws/aws-sdk-go-v2/internal/ini v1.8.1 // indirect
	github.com/aws/aws-sdk-go-v2/service/dynamodb v1.34.9 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/accept-encoding v1.12.0 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/endpoint-discovery v1.9.18 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/presigned-url v1.12.4 // indirect
	github.com/aws/aws-sdk-go-v2/service/kms v1.35.7 // indirect
	github.com/aws/aws-sdk-go-v2/service/sso v1.24.5 // indirect
	github.com/aws/aws-sdk-go-v2/service/ssooidc v1.28.4 // indirect
	github.com/aws/aws-sdk-go-v2/service/sts v1.32.4 // indirect
	github.com/jmespath/go-jmespath v0.4.0 // indirect
)

replace github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

replace github.com/smithy-lang/smithy-dafny/kmsv2 => ../../../../aws-sdks/kmsv2/runtimes/go/ImplementationFromDafny-go/

replace github.com/smithy-lang/smithy-dafny/ddbv2 => ../../../../aws-sdks/ddbv2/runtimes/go/ImplementationFromDafny-go/
