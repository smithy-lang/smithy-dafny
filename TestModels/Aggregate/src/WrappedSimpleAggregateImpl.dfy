include "../Model/SimpleAggregateTypesWrapped.dfy"

module {:extern "simple.aggregate.internaldafny.wrapped"} WrappedSimpleAggregateService refines WrappedAbstractSimpleAggregateService {
    import WrappedService = SimpleAggregate
    function method WrappedDefaultSimpleAggregateConfig(): SimpleAggregateConfig {
        SimpleAggregateConfig
    }
}
