namespace simple.composite.dependencyproject

@aws.polymorph#localService(
  sdkId: "DependencyProject",
  config: DependencyProjectConfig,
) service DependencyProject {
  version: "2021-11-01",
  resources: [],
  operations: [ SomeDependencyOperation ],
  errors: [ DependencyProjectEmptyError ],
}

structure DependencyProjectConfig {}

operation SomeDependencyOperation {
  input: SomeDependencyOperationInput,
  output: SomeDependencyOperationOutput,
}

structure SomeDependencyOperationInput {}

structure SomeDependencyOperationOutput {}

@error("client")
// Required until https://sim.amazon.com/issues/CrypTool-5263 is fixed
structure DependencyProjectEmptyError {}