include "./SimpleTypesImpl.dfy"

module {:extern "Dafny.Example.Simpletypes" } SimpleTypes refines AbstractExampleSimpletypesService {
    import Operations = SimpleTypesImpl

 function method DefaultEmptyConfig(): EmptyConfig {
    EmptyConfig
 }

 method SimpleTypes(config: EmptyConfig)
 returns (res: Result<SimpleTypesClient, Error>) {
    var client := new SimpleTypesClient(Operations.Config);
    return Success(client);
 }

 class SimpleTypesClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
 constructor(config: Operations.InternalConfig) {
    this.config := config;
    History := new ISimpleTypesServiceClientCallHistory();
    Modifies := Operations.ModifiesInternalConfig(config) + {History};

 }
 }

}