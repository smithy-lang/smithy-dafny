// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDafnyExternV2TypesWrapped.dfy"

//
replaceable module WrappedSimpleExternV2Service refines WrappedAbstractSimpleDafnyExternV2Service {
    import WrappedService = SimpleExternV2
    function method WrappedDefaultSimpleExternV2Config(): SimpleExternV2Config {
        WrappedService.DefaultSimpleExternV2Config()
    }
}
