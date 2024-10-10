// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.multiplemodels.primaryproject

use simple.multiplemodels.dependencyproject#SomeDependencyOperation

@aws.polymorph#localService(
  sdkId: "PrimaryProject",
  config: PrimaryProjectConfig,
  dependencies: [ simple.multiplemodels.dependencyproject#DependencyProject ]
) service PrimaryProject {
  version: "2021-11-01",
  resources: [],
  operations: [ SomePrimaryOperation, SomeDependencyOperation ],
  errors: [ PrimaryProjectError ],
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
structure PrimaryProjectError {
  @required
  message: String
}