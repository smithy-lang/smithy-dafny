include "../Model/SimpleAggregateTypesWrapped.dfy"

module {:extern "Dafny.Simple.Aggregate.Wrapped"} WrappedSimpleAggregateService refines WrappedAbstractSimpleAggregateService {
    import WrappedService = SimpleAggregate
    function method WrappedDefaultSimpleAggregateConfig(): SimpleAggregateConfig {
        SimpleAggregateConfig
    }
}