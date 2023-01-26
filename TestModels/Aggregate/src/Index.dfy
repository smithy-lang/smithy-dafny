include "SimpleAggregateImpl.dfy"

module {:extern "Dafny.Simple.Aggregate"} SimpleAggregate refines AbstractSimpleAggregateService {
    import Operations = SimpleAggregateImpl

    function method DefaultSimpleAggregateConfig(): SimpleAggregateConfig {
        SimpleAggregateConfig
    }

    method SimpleAggregate(config: SimpleAggregateConfig)
    returns (res: Result<SimpleAggregateClient, Error>) {
        var client := new SimpleAggregateClient(Operations.Config);
        return Success(client);
    }

    class SimpleAggregateClient... {
        predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
 constructor(config: Operations.InternalConfig) {
    this.config := config;
    History := new ISimpleAggregateClientCallHistory();
    Modifies := Operations.ModifiesInternalConfig(config) + {History};
 }
    }
}