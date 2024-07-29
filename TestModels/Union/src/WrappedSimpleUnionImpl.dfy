// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleUnionTypesWrapped.dfy"

module WrappedSimpleUnionService refines WrappedAbstractSimpleUnionService {
    import WrappedService = SimpleUnion
    function method WrappedDefaultSimpleUnionConfig(): SimpleUnionConfig {
        SimpleUnionConfig
    }
}
