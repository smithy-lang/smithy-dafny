include "SimpleErrorsImpl.dfy"

module {:extern "Dafny.Simple.Errors" } SimpleErrors refines AbstractSimpleErrorsService {
  import Operations = SimpleErrorsImpl

  function method DefaultSimpleErrorsConfig(): SimpleErrorsConfig {
    SimpleErrorsConfig
  }

  method SimpleErrors(config: SimpleErrorsConfig)
    returns (res: Result<SimpleErrorsClient, Error>)
  {
    var client := new SimpleErrorsClient(Operations.Config);
    return Success(client);
  }

  class SimpleErrorsClient... {
    predicate ValidState() {
       && Operations.ValidInternalConfig?(config)
       && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
       this.config := config;
       History := new ISimpleErrorsClientCallHistory();
       Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}