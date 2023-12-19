namespace simple.composite.primaryproject

use simple.composite.dependencyproject#SomeDependencyOperation

@aws.polymorph#localService(
  sdkId: "PrimaryProject",
  config: PrimaryProjectConfig,
) service PrimaryProject {
  version: "2021-11-01",
  resources: [],
  operations: [ SomePrimaryOperation, SomeDependencyOperation ],
  errors: [],
}

structure PrimaryProjectConfig {}

operation SomePrimaryOperation {
  input: SomePrimaryOperationInput,
  output: SomePrimaryOperationOutput,
}

structure SomePrimaryOperationInput {}

structure SomePrimaryOperationOutput {}