// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesSmithyStringTypesWrapped.dfy"

module {:extern "simple.types.smithystring.internaldafny.wrapped"} WrappedSimpleTypesSmithyStringService refines WrappedAbstractSimpleTypesSmithyStringService {
    import WrappedService = SimpleString
    function method WrappedDefaultSimpleStringConfig(): SimpleStringConfig {
        SimpleStringConfig
    }
}
