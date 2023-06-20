// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleUnionTypesWrapped.dfy"

module {:extern "simple.union.internaldafny.wrapped"} WrappedSimpleUnionService refines WrappedAbstractSimpleUnionService {
    import WrappedService = SimpleUnion
    function method WrappedDefaultSimpleUnionConfig(): SimpleUnionConfig {
        SimpleUnionConfig
    }
}
