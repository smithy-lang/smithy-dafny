include "../src/WrappedSimpleAggregateImpl.dfy"
include "SimpleAggregateImplTest.dfy"

module WrappedSimpleTypesStringTest {
    import WrappedSimpleAggregateService
    import SimpleAggregateImplTest
    import opened Wrappers
    method{:test} GetAggregate() {
        var client :- expect WrappedSimpleAggregateService.WrappedSimpleAggregate();
        SimpleAggregateImplTest.TestGetAggregate(client);
        SimpleAggregateImplTest.TestGetAggregateKnownValue(client);
    }
}