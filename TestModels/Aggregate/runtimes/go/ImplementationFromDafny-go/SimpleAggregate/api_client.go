// Code generated by smithy-go-codegen DO NOT EDIT.

package SimpleAggregate

import (
	"context"

	"github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/SimpleAggregateTypes"
)

type Client struct {
	DafnyClient *SimpleAggregateClient
}

func NewClient(clientConfig SimpleAggregateTypes.SimpleAggregateConfig_smithygenerated) (*Client, error) {
	var dafnyConfig = SimpleAggregateConfig_ToDafny(clientConfig)
	var dafny_response = Companion_Default___.SimpleAggregate(dafnyConfig)
	if dafny_response.Is_Failure() {
		panic("Client construction failed. This should never happen")
	}
	var dafnyClient = dafny_response.Extract().(*SimpleAggregateClient)
	client := &Client{dafnyClient}
	return client, nil
}

func (client *Client) GetAggregate(ctx context.Context, params SimpleAggregateTypes.GetAggregateInput_smithygenerated) (*SimpleAggregateTypes.GetAggregateOutput_smithygenerated, error) {
	err := params.Validate()
	if err != nil {
		opaqueErr := SimpleAggregateTypes.OpaqueError_smithygenerated{
			ErrObject: err,
		}
		return nil, opaqueErr
	}
	var dafny_request SimpleAggregateTypes.GetAggregateInput = GetAggregateInput_ToDafny(params)
	var dafny_response = client.DafnyClient.GetAggregate(dafny_request)

	if dafny_response.Is_Failure() {
		err := dafny_response.Dtor_error().(SimpleAggregateTypes.Error)
		return nil, Error_FromDafny(err)
	}
	var native_response = GetAggregateOutput_FromDafny(dafny_response.Extract().(SimpleAggregateTypes.GetAggregateOutput))
	return &native_response, nil

}

func (client *Client) GetAggregateKnownValueTest(ctx context.Context, params SimpleAggregateTypes.GetAggregateInput_smithygenerated) (*SimpleAggregateTypes.GetAggregateOutput_smithygenerated, error) {
	err := params.Validate()
	if err != nil {
		opaqueErr := SimpleAggregateTypes.OpaqueError_smithygenerated{
			ErrObject: err,
		}
		return nil, opaqueErr
	}
	var dafny_request SimpleAggregateTypes.GetAggregateInput = GetAggregateInput_ToDafny(params)
	var dafny_response = client.DafnyClient.GetAggregateKnownValueTest(dafny_request)

	if dafny_response.Is_Failure() {
		err := dafny_response.Dtor_error().(SimpleAggregateTypes.Error)
		return nil, Error_FromDafny(err)
	}
	var native_response = GetAggregateOutput_FromDafny(dafny_response.Extract().(SimpleAggregateTypes.GetAggregateOutput))
	return &native_response, nil

}
