namespace simple.composite.dependencyproject

@aws.polymorph#localService(
  sdkId: "DependencyProject",
  config: DependencyProjectConfig,
) service DependencyProject {
  version: "2021-11-01",
  resources: [],
  operations: [ SomeDependencyOperation ],
  errors: [],
}

structure DependencyProjectConfig {}

operation SomeDependencyOperation {
  input: SomeDependencyOperationInput,
  output: SomeDependencyOperationOutput,
}

structure SomeDependencyOperationInput {}

structure SomeDependencyOperationOutput {}
