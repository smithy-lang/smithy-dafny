// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleBooleanImpl.dfy"
include "SimpleBooleanImplTest.dfy"

module WrappedSimpleTypesBooleanTest {
    import WrappedSimpleTypesBooleanService
    import SimpleBooleanImplTest
    import opened Wrappers
    method{:test} GetBooleanTrue() {
        var client :- expect WrappedSimpleTypesBooleanService.WrappedSimpleBoolean();
        SimpleBooleanImplTest.TestGetBooleanTrue(client);
    }
    method{:test} GetBooleanFalse() {
        var client :- expect WrappedSimpleTypesBooleanService.WrappedSimpleBoolean();
        SimpleBooleanImplTest.TestGetBooleanFalse(client);
    }
}

/*
dafny \
    -vcsCores:2 \
    -compileTarget:py \
    -spillTargetCode:3 \
    -compile:0 \
    -optimizeErasableDatatypeWrapper:0 \
    -useRuntimeLib \
    -out runtimes/net/ImplementationFromDafny \
    ./src/Index.dfy \
    -library:/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/dafny-dependencies/StandardLibrary/src/Index.dfy \
*/