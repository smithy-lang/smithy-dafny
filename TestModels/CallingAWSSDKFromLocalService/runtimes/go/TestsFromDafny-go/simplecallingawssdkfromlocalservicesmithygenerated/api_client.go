// Code generated by smithy-go-codegen DO NOT EDIT.

package simplecallingawssdkfromlocalservicesmithygenerated

import (
	"context"

	"github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/SimpleCallingawssdkfromlocalserviceTypes"
	"github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/simplecallingawssdkfromlocalservicesmithygeneratedtypes"
)

type Client struct {
	DafnyClient *SimpleCallingawssdkfromlocalservice.SimpleCallingAWSSDKFromLocalServiceClient
}

func NewClient(clientConfig simplecallingawssdkfromlocalservicesmithygeneratedtypes.SimpleCallingAWSSDKFromLocalServiceConfig) (*Client, error) {
	var dafnyConfig = SimpleCallingAWSSDKFromLocalServiceConfig_ToDafny(clientConfig)
	var dafny_response = SimpleCallingawssdkfromlocalservice.Companion_Default___.SimpleCallingAWSSDKFromLocalService(dafnyConfig)
	if dafny_response.Is_Failure() {
		panic("Client construction failed. This should never happen")
	}
	var dafnyClient = dafny_response.Extract().(*SimpleCallingawssdkfromlocalservice.SimpleCallingAWSSDKFromLocalServiceClient)
	client := &Client{dafnyClient}
	return client, nil
}

func (client *Client) CallKMSEncrypt(ctx context.Context, params simplecallingawssdkfromlocalservicesmithygeneratedtypes.CallKMSEncryptInput) (*simplecallingawssdkfromlocalservicesmithygeneratedtypes.CallKMSEncryptOutput, error) {
	err := params.Validate()
	if err != nil {
		opaqueErr := simplecallingawssdkfromlocalservicesmithygeneratedtypes.OpaqueError{
			ErrObject: err,
		}
		return nil, opaqueErr
	}
	var dafny_request SimpleCallingawssdkfromlocalserviceTypes.CallKMSEncryptInput = CallKMSEncryptInput_ToDafny(params)
	var dafny_response = client.DafnyClient.CallKMSEncrypt(dafny_request)

	if dafny_response.Is_Failure() {
		err := dafny_response.Dtor_error().(SimpleCallingawssdkfromlocalserviceTypes.Error)
		return nil, Error_FromDafny(err)
	}
	var native_response = CallKMSEncryptOutput_FromDafny(dafny_response.Extract().(SimpleCallingawssdkfromlocalserviceTypes.CallKMSEncryptOutput))
	return &native_response, nil

}
