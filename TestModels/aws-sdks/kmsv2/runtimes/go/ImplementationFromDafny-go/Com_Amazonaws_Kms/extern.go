package Com_Amazonaws_Kms

import (
	"context"

	"github.com/aws/aws-sdk-go-v2/config"
	"github.com/aws/aws-sdk-go-v2/service/kms"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/v4/dafny"
	"github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	ComAmazonawsKmsTypes "github.com/smithy-lang/smithy-dafny/kmsv2/ComAmazonawsKmsTypes"
	"github.com/smithy-lang/smithy-dafny/kmsv2/KMSwrapped"
)

func (_static CompanionStruct_Default___) KMSClient() Wrappers.Result {
	cfg, err := config.LoadDefaultConfig(context.TODO())
	if err != nil {
		panic(err)
	}
	return Wrappers.Companion_Result_.Create_Success_(&KMSwrapped.Shim{Client: kms.NewFromConfig(cfg, func(o *kms.Options) {
		o.Region = "us-west-2"
	})})
}

func (_static CompanionStruct_Default___) RegionMatch(k ComAmazonawsKmsTypes.IKMSClient, S _dafny.Sequence) Wrappers.Option {
	var r = func() *string {
		var s string
		for i := _dafny.Iterate(S); ; {
			val, ok := i()
			if !ok {
				return &[]string{s}[0]
			} else {
				s = s + string(val.(_dafny.Char))
			}
		}
	}()
	var nc = k.(*KMSwrapped.Shim).Client
	return Wrappers.Companion_Option_.Create_Some_(nc.Options().Region == *r)
}
