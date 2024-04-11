// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../dafny-dependencies/StandardLibrary/src/Index.dfy"
include "../src/Index.dfy"
abstract module WrappedAbstractSimpleCodegenpatchesService {
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened UTF8
  import opened Types = SimpleCodegenpatchesTypes
  import WrappedService : AbstractSimpleCodegenpatchesService
  function method WrappedDefaultCodegenPatchesConfig(): CodegenPatchesConfig
  method {:extern} WrappedCodegenPatches(config: CodegenPatchesConfig := WrappedDefaultCodegenPatchesConfig())
    returns (res: Result<ICodegenPatchesClient, Error>)
    ensures res.Success? ==>
              && fresh(res.value)
              && fresh(res.value.Modifies)
              && fresh(res.value.History)
              && res.value.ValidState()
}
