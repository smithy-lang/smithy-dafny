// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../smithy-polymorph/lib/std/src/Index.dfy"
 include "../src/Index.dfy"
 abstract module WrappedAbstractExampleSimpletypesService {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = ExampleSimpletypesTypes
 import WrappedService : AbstractExampleSimpletypesService
 function method WrappedDefaultEmptyConfig(): EmptyConfig
 method {:extern} WrappedSimpleTypes(config: EmptyConfig := WrappedDefaultEmptyConfig())
 returns (res: Result<ISimpleTypesServiceClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
}
