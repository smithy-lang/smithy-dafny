// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesSmithyLongTypesWrapped.dfy"

module WrappedSimpleTypesLongService refines WrappedAbstractSimpleTypesSmithyLongService {
    import WrappedService = SimpleLong
    function method WrappedDefaultSimpleLongConfig(): SimpleLongConfig {
        SimpleLongConfig
    }
}
