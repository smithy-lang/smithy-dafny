module github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/test

go 1.23.0

require github.com/dafny-lang/DafnyStandardLibGo v0.0.0

require (
	github.com/aws/smithy-go v1.20.4
	github.com/dafny-lang/DafnyStandardLibGo v0.0.0
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.8.0
	github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService v0.0.0
	github.com/smithy-lang/smithy-dafny/ddb v0.0.0
	github.com/smithy-lang/smithy-dafny/kms v0.0.0
)

require (
	github.com/aws/aws-sdk-go-v2 v1.30.5 // indirect
	github.com/aws/aws-sdk-go-v2/config v1.27.33 // indirect
	github.com/aws/aws-sdk-go-v2/credentials v1.17.32 // indirect
	github.com/aws/aws-sdk-go-v2/feature/ec2/imds v1.16.13 // indirect
	github.com/aws/aws-sdk-go-v2/internal/configsources v1.3.17 // indirect
	github.com/aws/aws-sdk-go-v2/internal/endpoints/v2 v2.6.17 // indirect
	github.com/aws/aws-sdk-go-v2/internal/ini v1.8.1 // indirect
	github.com/aws/aws-sdk-go-v2/service/dynamodb v1.34.9 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/accept-encoding v1.11.4 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/endpoint-discovery v1.9.18 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/presigned-url v1.11.19 // indirect
	github.com/aws/aws-sdk-go-v2/service/kms v1.35.7 // indirect
	github.com/aws/aws-sdk-go-v2/service/sso v1.22.7 // indirect
	github.com/aws/aws-sdk-go-v2/service/ssooidc v1.26.7 // indirect
	github.com/aws/aws-sdk-go-v2/service/sts v1.30.7 // indirect
	github.com/jmespath/go-jmespath v0.4.0 // indirect
)

replace github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService v0.0.0 => ../ImplementationFromDafny-go

replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

replace github.com/smithy-lang/smithy-dafny/kms => /Users/rishavkj/Documents/Storage/Team-Repos/smithy-dafny/TestModels/aws-sdks/kms/runtimes/go/ImplementationFromDafny-go/

replace github.com/smithy-lang/smithy-dafny/ddb => /Users/rishavkj/Documents/Storage/Team-Repos/smithy-dafny/TestModels/aws-sdks/ddb/runtimes/go/ImplementationFromDafny-go/
