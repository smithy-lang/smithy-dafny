// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleAggregateTypesWrapped.dfy"

module {:extern "simple.aggregate.internaldafny.wrapped"} WrappedSimpleAggregateService refines WrappedAbstractSimpleAggregateService {
    import WrappedService = SimpleAggregate
    function method WrappedDefaultSimpleAggregateConfig(): SimpleAggregateConfig {
        SimpleAggregateConfig
    }
}
