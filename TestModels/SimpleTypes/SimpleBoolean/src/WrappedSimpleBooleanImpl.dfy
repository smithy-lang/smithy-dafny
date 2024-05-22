// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesBooleanTypesWrapped.dfy"

module {:extern "simple.types.boolean.internaldafny.wrapped"} WrappedSimpleTypesBooleanService refines WrappedAbstractSimpleTypesBooleanService {
    import WrappedService = SimpleBoolean
    function method WrappedDefaultSimpleBooleanConfig(): SimpleBooleanConfig {
        SimpleBooleanConfig
    }
}
