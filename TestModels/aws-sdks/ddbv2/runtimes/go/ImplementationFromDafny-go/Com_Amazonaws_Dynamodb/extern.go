package Com_Amazonaws_Dynamodb

import (
	"context"

	"github.com/aws/aws-sdk-go-v2/config"
	"github.com/aws/aws-sdk-go-v2/service/dynamodb"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/v4/dafny"
	"github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	"github.com/smithy-lang/smithy-dafny/ddbv2/ComAmazonawsDynamodbTypes"
	"github.com/smithy-lang/smithy-dafny/ddbv2/DynamoDBwrapped"
)

func (_static *CompanionStruct_Default___) DynamoDBClient() Wrappers.Result {
	cfg, err := config.LoadDefaultConfig(context.TODO())
	if err != nil {
		panic(err)
	}
	return Wrappers.Companion_Result_.Create_Success_(&DynamoDBwrapped.Shim{Client: dynamodb.NewFromConfig(cfg, func(o *dynamodb.Options) {
		o.Region = "us-west-2"
	})})
}

func (_static *CompanionStruct_Default___) RegionMatch(k ComAmazonawsDynamodbTypes.IDynamoDBClient, S _dafny.Sequence) Wrappers.Option {
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
	var nc = k.(*DynamoDBwrapped.Shim).Client
	return Wrappers.Companion_Option_.Create_Some_(nc.Options().Region == *r)
}
