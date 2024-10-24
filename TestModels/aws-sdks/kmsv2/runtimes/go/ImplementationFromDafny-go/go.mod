module github.com/smithy-lang/smithy-dafny/kmsv2

go 1.23.0

replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

require (
	github.com/aws/aws-sdk-go-v2/config v1.28.0
	github.com/aws/aws-sdk-go-v2/service/kms v1.35.5
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.8.0
	github.com/dafny-lang/DafnyStandardLibGo v0.0.0-00010101000000-000000000000
	github.com/aws/smithy-go v1.22.0
)

require (
	github.com/aws/aws-sdk-go-v2 v1.32.2 // indirect
	github.com/aws/aws-sdk-go-v2/credentials v1.17.41 // indirect
	github.com/aws/aws-sdk-go-v2/feature/ec2/imds v1.16.17 // indirect
	github.com/aws/aws-sdk-go-v2/internal/configsources v1.3.21 // indirect
	github.com/aws/aws-sdk-go-v2/internal/endpoints/v2 v2.6.21 // indirect
	github.com/aws/aws-sdk-go-v2/internal/ini v1.8.1 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/accept-encoding v1.12.0 // indirect
	github.com/aws/aws-sdk-go-v2/service/internal/presigned-url v1.12.2 // indirect
	github.com/aws/aws-sdk-go-v2/service/sso v1.24.2 // indirect
	github.com/aws/aws-sdk-go-v2/service/ssooidc v1.28.2 // indirect
	github.com/aws/aws-sdk-go-v2/service/sts v1.32.2 // indirect
)
