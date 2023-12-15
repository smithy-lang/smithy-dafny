namespace simple.composite.primaryproject

use simple.composite.dependencyproject#DependencyService
use simple.composite.dependencyproject#IdentityOperationInput
use simple.composite.dependencyproject#IdentityOperationOutput

@aws.polymorph#localService(
  sdkId: "PrimaryProject",
  config: PrimaryProjectConfig,
) service PrimaryProject {
  version: "2021-11-01",
  resources: [],
  operations: [ IdentityOperation, IdentityOperationOnDependency ],
  errors: [],
}

structure PrimaryProjectConfig {}

operation IdentityOperation {
  input: IdentityOperationInput,
  output: IdentityOperationOutput,
}

operation IdentityOperationOnDependency {
  input: IdentityOperationInput,
  output: IdentityOperationOutput,
}