namespace simple.composite.primaryproject

use simple.composite.dependencyproject#SomeDependencyOperation

@aws.polymorph#localService(
  sdkId: "PrimaryProject",
  config: PrimaryProjectConfig,
) service PrimaryProject {
  version: "2021-11-01",
  resources: [],
  operations: [ SomePrimaryOperation, SomeDependencyOperation ],
  errors: [ PrimaryProjectEmptyError ],
}

structure PrimaryProjectConfig {}

operation SomePrimaryOperation {
  input: SomePrimaryOperationInput,
  output: SomePrimaryOperationOutput,
}

structure SomePrimaryOperationInput {}

structure SomePrimaryOperationOutput {}

@error("client")
// Required until https://sim.amazon.com/issues/CrypTool-5263 is fixed
structure PrimaryProjectEmptyError {}