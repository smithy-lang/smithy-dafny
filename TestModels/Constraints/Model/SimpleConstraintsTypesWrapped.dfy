// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../../../../../../../Volumes/workplace/ryan-new-world/polymorph/TestModels/dafny-dependencies/StandardLibrary/src/Index.dfy"
 include "../src/Index.dfy"
 abstract module WrappedAbstractSimpleConstraintsService {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleConstraintsTypes
 import WrappedService : AbstractSimpleConstraintsService
 function method WrappedDefaultSimpleConstraintsConfig(): SimpleConstraintsConfig
 method {:extern} WrappedSimpleConstraints(config: SimpleConstraintsConfig := WrappedDefaultSimpleConstraintsConfig())
 returns (res: Result<ISimpleConstraintsClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
}
