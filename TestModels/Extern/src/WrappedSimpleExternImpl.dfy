// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDafnyExternTypesWrapped.dfy"

module WrappedSimpleExternService refines WrappedAbstractSimpleDafnyExternService {
    import WrappedService = SimpleExtern
    function method WrappedDefaultSimpleExternConfig(): SimpleExternConfig {
        WrappedService.DefaultSimpleExternConfig()
    }
}
