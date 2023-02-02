include "SimpleEnumImpl.dfy"

module {:extern "Dafny.Simple.Types.Enum" } SimpleEnum refines AbstractSimpleTypesEnumService {
    import Operations = SimpleEnumImpl

 function method DefaultSimpleEnumConfig(): SimpleEnumConfig {
    SimpleEnumConfig
 }

 method SimpleEnum(config: SimpleEnumConfig)
 returns (res: Result<SimpleEnumClient, Error>) {
    var client := new SimpleEnumClient(Operations.Config);
    return Success(client);
 }

 class SimpleEnumClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
 constructor(config: Operations.InternalConfig) {
    this.config := config;
    History := new ISimpleTypesEnumClientCallHistory();
    Modifies := Operations.ModifiesInternalConfig(config) + {History};

 }
 }

}