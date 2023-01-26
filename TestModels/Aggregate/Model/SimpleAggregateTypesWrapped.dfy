// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../DafnyLib/std/src/Index.dfy"
 include "../src/Index.dfy"
 abstract module WrappedAbstractSimpleAggregateService {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleAggregateTypes
 import WrappedService : AbstractSimpleAggregateService
 function method WrappedDefaultSimpleAggregateConfig(): SimpleAggregateConfig
 method {:extern} WrappedSimpleAggregate(config: SimpleAggregateConfig := WrappedDefaultSimpleAggregateConfig())
 returns (res: Result<ISimpleAggregateClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
}
