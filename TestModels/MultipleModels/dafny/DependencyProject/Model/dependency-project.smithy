// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.multiplemodels.dependencyproject

@aws.polymorph#localService(
  sdkId: "DependencyProject",
  config: DependencyProjectConfig,
)
service DependencyProject {
  version: "2021-11-01",
  resources: [],
  operations: [ SomeDependencyOperation ],
  errors: [ DependencyProjectError ],
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
structure DependencyProjectError {
  @required
  message: String
}