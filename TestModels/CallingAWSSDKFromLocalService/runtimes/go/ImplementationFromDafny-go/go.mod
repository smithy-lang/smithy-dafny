module github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService

go 1.23.0

require github.com/dafny-lang/DafnyStandardLibGo v0.0.0

require github.com/dafny-lang/DafnyRuntimeGo v0.0.0

require github.com/smithy-lang/smithy-dafny/kms v0.0.0

require (
	github.com/aws/aws-sdk-go-v2 v1.30.5 // indirect
	github.com/aws/aws-sdk-go-v2/internal/configsources v1.3.17 // indirect
	github.com/aws/aws-sdk-go-v2/internal/endpoints/v2 v2.6.17 // indirect
	github.com/aws/aws-sdk-go-v2/service/kms v1.35.7 // indirect
	github.com/aws/smithy-go v1.20.4 // indirect
)

//TODO: Drop this after Dafny fixes the https://t.corp.amazon.com/P150784381
replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../DafnyRuntimeGo/

replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

replace github.com/smithy-lang/smithy-dafny/kms => /Users/rishavkj/Documents/Storage/Team-Repos/smithy-dafny/TestModels/aws-sdks/kms/runtimes/go/ImplementationFromDafny-go/
