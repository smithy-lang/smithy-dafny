include "SimpleStringImpl.dfy"

module {:extern "Dafny.Simple.Types.String" } SimpleString refines AbstractSimpleTypesStringService {
    import Operations = SimpleStringImpl

    function method DefaultSimpleStringConfig(): SimpleStringConfig {
        SimpleStringConfig
    }

    method SimpleString(config: SimpleStringConfig)
    returns (res: Result<SimpleStringClient, Error>) {
        var client := new SimpleStringClient(Operations.Config);
        return Success(client);
    }

    class SimpleStringClient... {
        predicate ValidState()
        {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }
        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ISimpleTypesStringClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}