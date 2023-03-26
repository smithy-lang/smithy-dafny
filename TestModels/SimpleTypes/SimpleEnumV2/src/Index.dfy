include "SimpleEnumImpl.dfy"

module {:extern "Dafny.Simple.Types.EnumV2" } SimpleEnumV2 refines AbstractSimpleTypesEnumV2Service {
    import Operations = SimpleEnumV2Impl

 function method DefaultSimpleEnumV2Config(): SimpleEnumV2Config {
    SimpleEnumV2Config
 }

 method SimpleEnumV2(config: SimpleEnumV2Config)
 returns (res: Result<SimpleEnumV2Client, Error>) {
    var client := new SimpleEnumV2Client(Operations.Config);
    return Success(client);
 }

 class SimpleEnumV2Client... {
   predicate ValidState()
   {
     && Operations.ValidInternalConfig?(config)
     && Modifies == Operations.ModifiesInternalConfig(config) + {History}
   }

   constructor(config: Operations.InternalConfig)
   {
     this.config := config;
     History := new ISimpleTypesEnumV2ClientCallHistory();
     Modifies := Operations.ModifiesInternalConfig(config) + {History};
   }
 }
}
