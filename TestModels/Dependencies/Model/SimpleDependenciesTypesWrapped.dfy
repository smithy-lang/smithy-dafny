// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../dafny-dependencies/StandardLibrary/src/Index.dfy"
 include "../src/Index.dfy"
 abstract module WrappedAbstractSimpleDependenciesService {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleDependenciesTypes
 import WrappedService : AbstractSimpleDependenciesService
 function method WrappedDefaultSimpleDependenciesConfig(): SimpleDependenciesConfig
 method {:extern} WrappedSimpleDependencies(config: SimpleDependenciesConfig := WrappedDefaultSimpleDependenciesConfig())
 returns (res: Result<ISimpleDependenciesClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
}
