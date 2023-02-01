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
        ValidateInput(input);
        var res := GetAggregateOutput(simpleStringList := input.simpleStringList,
                                        structureList := input.structureList,
                                        simpleStringMap := input.simpleStringMap,
                                        simpleIntegerMap := input.simpleIntegerMap,
                                        nestedStructure := input.nestedStructure);
        return Success(res);
    }

    method ValidateInput(input: GetAggregateInput) {
        var stringList := input.simpleStringList.UnwrapOr([]);
        expect |stringList| >= 0;
        for i := 0 to |stringList| {
            var inputElement := stringList[i];
            expect "" <= inputElement;
        }

        var structureList := input.structureList.UnwrapOr([]);
        expect |structureList| >= 0;
        for i := 0 to |structureList| {
            var inputElement := structureList[i];
            expect "" <= inputElement.stringValue.UnwrapOr("");
            expect 0 <= inputElement.integerValue.UnwrapOr(0) || 0 >= inputElement.integerValue.UnwrapOr(0);
        }
        var simpleStringMap := input.simpleStringMap.UnwrapOr(map[]);
        expect |simpleStringMap| >= 0;
        var simpleIntegerMap := input.simpleIntegerMap.UnwrapOr(map[]);
        expect |simpleIntegerMap| >= 0;
    }
}