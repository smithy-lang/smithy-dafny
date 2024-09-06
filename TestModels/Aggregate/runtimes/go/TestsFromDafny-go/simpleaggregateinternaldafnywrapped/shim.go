// Code generated by smithy-go-codegen DO NOT EDIT.

package SimpleAggregateinternaldafnywrapped

import (
	"context"

	"github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	"github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/SimpleAggregate"
	"github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/SimpleAggregateinternaldafnytypes"
)

type Shim struct {
	SimpleAggregateinternaldafnytypes.ISimpleAggregateClient
	client *SimpleAggregate.Client
}

func WrappedSimpleAggregate(inputConfig SimpleAggregateinternaldafnytypes.SimpleAggregateConfig) Wrappers.Result {
	var nativeConfig = SimpleAggregate.SimpleAggregateConfig_FromDafny(inputConfig)
	var nativeClient, nativeError = SimpleAggregate.NewClient(nativeConfig)
	if nativeError != nil {
		return Wrappers.Companion_Result_.Create_Failure_(SimpleAggregateinternaldafnytypes.Companion_Error_.Create_Opaque_(nativeError))
	}
	return Wrappers.Companion_Result_.Create_Success_(&Shim{client: nativeClient})
}

func (shim *Shim) GetAggregate(input SimpleAggregateinternaldafnytypes.GetAggregateInput) Wrappers.Result {
	var native_request = SimpleAggregate.GetAggregateInput_FromDafny(input)
	var native_response, native_error = shim.client.GetAggregate(context.Background(), native_request)
	if native_error != nil {
		return Wrappers.Companion_Result_.Create_Failure_(SimpleAggregate.Error_ToDafny(native_error))
	}
	return Wrappers.Companion_Result_.Create_Success_(SimpleAggregate.GetAggregateOutput_ToDafny(*native_response))
}

func (shim *Shim) GetAggregateKnownValueTest(input SimpleAggregateinternaldafnytypes.GetAggregateInput) Wrappers.Result {
	var native_request = SimpleAggregate.GetAggregateInput_FromDafny(input)
	var native_response, native_error = shim.client.GetAggregateKnownValueTest(context.Background(), native_request)
	if native_error != nil {
		return Wrappers.Companion_Result_.Create_Failure_(SimpleAggregate.Error_ToDafny(native_error))
	}
	return Wrappers.Companion_Result_.Create_Success_(SimpleAggregate.GetAggregateOutput_ToDafny(*native_response))
}
