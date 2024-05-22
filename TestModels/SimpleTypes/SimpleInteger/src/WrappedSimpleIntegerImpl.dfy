// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesIntegerTypesWrapped.dfy"

module {:extern "simple.types.integer.internaldafny.wrapped"} WrappedSimpleTypesIntegerService refines WrappedAbstractSimpleTypesIntegerService {
    import WrappedService = SimpleInteger
    function method WrappedDefaultSimpleIntegerConfig(): SimpleIntegerConfig {
        SimpleIntegerConfig
    }
}
