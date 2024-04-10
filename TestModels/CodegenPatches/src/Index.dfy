// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "CodegenPatchesImpl.dfy"

module {:extern "simple.codegenpatches.internaldafny" } CodegenPatches refines AbstractSimpleCodegenpatchesService {
  import Operations = CodegenPatchesImpl

  function method DefaultCodegenPatchesConfig(): CodegenPatchesConfig {
    CodegenPatchesConfig
  }

  method CodegenPatches(config: CodegenPatchesConfig)
    returns (res: Result<CodegenPatchesClient, Error>)
  {
    var client := new CodegenPatchesClient(Operations.Config);
    return Success(client);
  }

  class CodegenPatchesClient... {
    predicate ValidState() {
       && Operations.ValidInternalConfig?(config)
       && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
       this.config := config;
       History := new ICodegenPatchesClientCallHistory();
       Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
