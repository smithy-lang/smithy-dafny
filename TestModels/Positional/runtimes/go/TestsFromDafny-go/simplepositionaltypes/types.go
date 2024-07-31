// Code generated by smithy-go-codegen DO NOT EDIT.

package simplepositionaltypes

import (
	"fmt"
)

type GetResourceInput struct {
	Name *string
}

func (input GetResourceInput) Validate() error {
	if input.Name == nil {
		return fmt.Errorf("Name is required but has a nil value.")
	}

	return nil
}

type SimpleResourceReference struct {
}

func (input SimpleResourceReference) Validate() error {
	return nil
}

type GetResourceOutput struct {
	Output ISimpleResource
}

func (input GetResourceOutput) Validate() error {

	return nil
}

type GetResourcePositionalInput struct {
	Name *string
}

func (input GetResourcePositionalInput) Validate() error {
	if input.Name == nil {
		return fmt.Errorf("Name is required but has a nil value.")
	}

	return nil
}

type GetResourcePositionalOutput struct {
	Output ISimpleResource
}

func (input GetResourcePositionalOutput) Validate() error {

	return nil
}

type SimplePositionalConfig struct {
}

func (input SimplePositionalConfig) Validate() error {
	return nil
}

type SimplePositionalBaseException interface {
	// This is a dummy method to allow type assertion since Go empty interfaces
	// aren't useful for type assertion checks. No concrete class is expected to implement
	// this method. This is also not exported.
	interfaceBindingMethod()
}

type ISimpleResource interface {
	GetName(GetNameInput) (*GetNameOutput, error)
}

type GetNameInput struct {
}

func (input GetNameInput) Validate() error {
	return nil
}

type GetNameOutput struct {
	Name *string
}

func (input GetNameOutput) Validate() error {
	if input.Name == nil {
		return fmt.Errorf("Name is required but has a nil value.")
	}

	return nil
}
