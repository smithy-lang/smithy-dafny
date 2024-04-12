// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.dependencies

use simple.resources#SimpleResources
use simple.constraints#SimpleConstraints
use simple.extendable.resources#SimpleExtendableResources
// TODO: Uncomment out as part of https://sim.amazon.com/issues/CrypTool-5231
//use simple.errors#SimpleErrors

@aws.polymorph#localService(
  sdkId: "SimpleDependencies",
  config: SimpleDependenciesConfig,
  dependencies: [
    SimpleResources,
    SimpleConstraints,
    SimpleExtendableResources,
    // TODO: Uncomment out as part of https://sim.amazon.com/issues/CrypTool-5231
    // SimpleErrors
  ]
)
service SimpleDependencies {
  version: "2021-11-01",
  resources: [],
  operations: [
    GetSimpleResource,
    UseSimpleResource,
    UseLocalConstraintsService,
    UseLocalExtendableResource,
    LocalExtendableResourceAlwaysModeledError,
    LocalExtendableResourceAlwaysMultipleErrors,
    LocalExtendableResourceAlwaysNativeError,
  ],
  errors: [],
}

@aws.polymorph#reference(service: simple.resources#SimpleResources)
structure SimpleResourceServiceReference {}

@aws.polymorph#reference(service: simple.constraints#SimpleConstraints)
structure SimpleConstraintsServiceReference {}

structure SimpleDependenciesConfig {
  // This config is used to create a local SimpleResourceService
  simpleResourcesConfig: simple.resources#SimpleResourcesConfig,
  // This is to pass a service in a config
  simpleConstraintsServiceReference: SimpleConstraintsServiceReference,
  // This is to pass a resource reference in a config
  extendableResourceReference: simple.extendable.resources#ExtendableResourceReference,
  // This is just testing that the Dafny types will line up.
  specialString: simple.constraints#MyString
}

// This operation MUST call the local SimpleResourceService
// that is stored _only_ in the InternalConfig
operation GetSimpleResource {
  input: simple.resources#GetResourcesInput,
  output: simple.resources#GetResourcesOutput,
}

// This operation MUST use a SimpleResourceReference
// and return the output
operation UseSimpleResource {
  input: UseSimpleResourceInput,
  output: simple.resources#GetResourceDataOutput,
}

structure UseSimpleResourceInput {
  @required
  value: simple.resources#SimpleResourceReference,
  @required
  input: simple.resources#GetResourceDataInput,
}

// This operation MUST call the local simpleConstraintsServiceReference
// that is stored _only_ in the InternalConfig
// This tests service wrapping/unwrapping
operation UseLocalConstraintsService {
  input: simple.constraints#GetConstraintsInput,
  output: simple.constraints#GetConstraintsOutput,
}

// This operation MUST call use the local extendableResourceReference
// with the input and return the output
operation UseLocalExtendableResource {
  input: simple.extendable.resources#GetExtendableResourceDataInput,
  output: simple.extendable.resources#UseExtendableResourceOutput,
}

// This operation MUST call the local ExtendableResource and wrap the error
operation LocalExtendableResourceAlwaysModeledError {
  input: simple.extendable.resources#GetExtendableResourceErrorsInput,
  output: simple.extendable.resources#GetExtendableResourceErrorsOutput,
}

// This operation MUST call the local ExtendableResource and wrap the error
operation LocalExtendableResourceAlwaysMultipleErrors {
  input: simple.extendable.resources#GetExtendableResourceErrorsInput,
  output: simple.extendable.resources#GetExtendableResourceErrorsOutput,
}

// This operation MUST call the local ExtendableResource and wrap the error
operation LocalExtendableResourceAlwaysNativeError {
  input: simple.extendable.resources#GetExtendableResourceErrorsInput,
  output: simple.extendable.resources#GetExtendableResourceErrorsOutput,
}
