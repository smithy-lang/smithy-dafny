include "../Model/SimpleExternTypes.dfy"
include "ExternConstructor.dfy"

module SimpleExternImpl refines AbstractSimpleExternOperations  {
    import opened ExternConstructor
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
    method{:extern "GetExtern"} GetExtern(config: InternalConfig, input: GetExternInput)
        returns (output: Result<GetExternOutput, Error>)

    method{:extern "ExternMustError"} ExternMustError(config: InternalConfig, input: ExternMustErrorInput)
        returns (output: Result<ExternMustErrorOutput, Error>)

    method UseClassExtern(config: InternalConfig, input: UseClassExternInput)
        returns (output: Result<UseClassExternOutput, Error>) {
            // This class constructor is implemented as extern and hence it might be possible
            // that the underlying runtime can actualy throw errors in constructors (say C#).
            // In these cases, dafny would halt the whole program (since constructor can't have a return type
            // and can't return the error).
            var externClassObject := new ExternConstructor.ExternConstructorClass();
            return Success(UseClassExternOutput(value:=input.value));
        }
}