include "../Model/SimpleExternTypes.dfy"

module SimpleExternImpl refines AbstractSimpleExternOperations  {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetExternEnsuresPublicly(input: GetExternInput, output: Result<GetExternOutput, Error>) {
        true
    }
    predicate UseClassExternEnsuresPublicly(input: UseClassExternInput, output: Result<UseClassExternOutput, Error>) {
        true
    }
    predicate ExternMustErrorEnsuresPublicly(input: ExternMustErrorInput, output: Result<ExternMustErrorOutput, Error>) {
        true
    }
    method{:extern "GetExtern"} GetExtern ( config: InternalConfig,  input: GetExternInput )
        returns (output: Result<GetExternOutput, Error>)

    method UseClassExtern ( config: InternalConfig,  input: UseClassExternInput )
        returns (output: Result<UseClassExternOutput, Error>)
    {  
       
    }
    
    method ExternMustError ( config: InternalConfig,  input: ExternMustErrorInput )
        returns (output: Result<ExternMustErrorOutput, Error>)
    {  
       
    }
}