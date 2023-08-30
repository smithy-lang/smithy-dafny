// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../dafny-dependencies/StandardLibrary/src/Index.dfy"
 include "../src/Index.dfy"
 abstract module WrappedAbstractSimpleTypesSmithyStringService {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleTypesSmithyStringTypes
 import WrappedService : AbstractSimpleTypesSmithyStringService
 function method WrappedDefaultSimpleStringConfig(): SimpleStringConfig
 method {:extern} WrappedSimpleString(config: SimpleStringConfig := WrappedDefaultSimpleStringConfig())
 returns (res: Result<ISimpleTypesStringClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
}
