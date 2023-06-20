// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesSmithyLongTypesWrapped.dfy"

module {:extern "simple.types.smithylong.internaldafny.wrapped"} WrappedSimpleTypesLongService refines WrappedAbstractSimpleTypesSmithyLongService {
    import WrappedService = SimpleLong
    function method WrappedDefaultSimpleLongConfig(): SimpleLongConfig {
        SimpleLongConfig
    }
}
