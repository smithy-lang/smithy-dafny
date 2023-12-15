namespace simple.composite.dependencyproject

@aws.polymorph#localService(
  sdkId: "DependencyProject",
  config: DependencyProjectConfig,
) service DependencyProject {
  version: "2021-11-01",
  resources: [],
  operations: [ IdentityOperation ],
  errors: [],
}

structure DependencyProjectConfig {}

operation IdentityOperation {
  input: IdentityOperationInput,
  output: IdentityOperationOutput,
}

structure IdentityOperationInput {
  value: String
}

structure IdentityOperationOutput {
  value: String
}