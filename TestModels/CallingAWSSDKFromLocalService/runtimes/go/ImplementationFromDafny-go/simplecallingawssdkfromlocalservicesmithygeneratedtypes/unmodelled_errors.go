// Code generated by smithy-go-codegen DO NOT EDIT.

package simplecallingawssdkfromlocalservicesmithygeneratedtypes

import (
	"fmt"
)

type CollectionOfErrors struct {
	SimpleCallingAWSSDKFromLocalServiceBaseException
	ListOfErrors []error
	Message      string
}

func (e CollectionOfErrors) Error() string {
	return fmt.Sprintf("message: %s\n err %v", e.Message, e.ListOfErrors)
}

type OpaqueError struct {
	SimpleCallingAWSSDKFromLocalServiceBaseException
	ErrObject interface{}
}

func (e OpaqueError) Error() string {
	return fmt.Sprintf("message: %v", e.ErrObject)
}
