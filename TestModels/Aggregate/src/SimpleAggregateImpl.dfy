include "../Model/SimpleAggregateTypes.dfy"

module SimpleAggregateImpl refines AbstractSimpleAggregateOperations {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>) {
        true
    }
    method GetAggregate(config: InternalConfig, input: GetAggregateInput )
    returns (output: Result<GetAggregateOutput, Error>) {
        var res := GetAggregateOutput(simpleStringList := input.simpleStringList,
                                        structureList := input.structureList,
                                        SimpleStringMap := input.SimpleStringMap,
                                        SimpleIntegerMap := input.SimpleIntegerMap,
                                        very := input.very);
        return Success(res);
    }
}