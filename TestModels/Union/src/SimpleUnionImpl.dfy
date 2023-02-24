include "../Model/SimpleUnionTypes.dfy"

module SimpleUnionImpl refines AbstractSimpleUnionOperations  {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetUnionEnsuresPublicly(input: GetUnionInput, output: Result<GetUnionOutput, Error>) {
        true
    }
    method GetUnion ( config: InternalConfig,  input: GetUnionInput )
      returns (output: Result<GetUnionOutput, Error>)
    {
        var res := GetUnionOutput(union := input.union);

        return Success(res);
    }
}