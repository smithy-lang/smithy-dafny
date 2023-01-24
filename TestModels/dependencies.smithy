namespace simple.dependencies

@aws.polymorph#localService(
  sdkId: "SimpleDependencies",
  config: SimpleDependenciesConfig,
)
service SimpleDependencies {
  version: "2021-11-01",
  resources: [],
  operations: [
    GetSimpleResource,
    UseSimpeResource,
    UseLocalExtendableResource,
    LocalExtendableResourceAlwaysError,
    LocalExtendableResourceAlwaysMultipuleErrors,
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
operation UseSimpeResource {
  input: simple.resources#GetResourceDataInput,
  output: simple.resources#GetResourceDataOutput,
}

structure UseSimpeResourceInput {
  @required
  value: simple.resources#SimpleResourceReference,
  @required
  input: simple.resources#GetResourceDataInput,
}

// This operation MUST call use the local extendableResourceReference
// with the input and return the output
operation UseLocalExtendableResource {
  input: simple.extendable.resources#GetExtendableResourceDataInput,
  output: simple.extendable.resources#UseExtendableResourcesOutput,
}

// This operation MUST call the local ExtendableResource and wrap the error
operation LocalExtendableResourceAlwaysError {
  input: simple.extendable.resources#GetExtendableResourceErrorsInput,
  output: simple.extendable.resources#GetExtendableResourceErrorsOutput,
}

// This operation MUST call the local ExtendableResource and wrap the error
operation LocalExtendableResourceAlwaysMultipuleErrors {
  input: simple.extendable.resources#GetExtendableResourceErrorsInput,
  output: simple.extendable.resources#GetExtendableResourceErrorsOutput,
}

// This operation MUST call the local ExtendableResource and wrap the error
operation LocalExtendableResourceAlwaysNativeError {
  input: simple.extendable.resources#GetExtendableResourceErrorsInput,
  output: simple.extendable.resources#GetExtendableResourceErrorsOutput,
}

