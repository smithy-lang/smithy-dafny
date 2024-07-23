// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesSmithyStringTypesWrapped.dfy"

module WrappedSimpleTypesStringService refines WrappedAbstractSimpleTypesSmithyStringService {
    import WrappedService = SimpleString
    function method WrappedDefaultSimpleStringConfig(): SimpleStringConfig {
        SimpleStringConfig
    }
}
