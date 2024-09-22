// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
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
    predicate GetAggregateKnownValueTestEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>) {
        true
    }
    method GetAggregate(config: InternalConfig, input: GetAggregateInput )
    returns (output: Result<GetAggregateOutput, Error>) {
        var res := GetAggregateOutput(simpleStringList := input.simpleStringList,
                                        structureList := input.structureList,
                                        simpleStringMap := input.simpleStringMap,
                                        simpleIntegerMap := input.simpleIntegerMap,
                                        nestedStructure := input.nestedStructure);
        return Success(res);
    }

    // This method is only used for known-value testing. See "Known Value Tests" inside TestModels' README file.
    method GetAggregateKnownValueTest(config: InternalConfig, input: GetAggregateInput )
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
        expect input.simpleStringList.UnwrapOr([]) == ["Test"];
        expect input.simpleStringMap.UnwrapOr(map[]) == map["Test1" := "Success"];
        expect input.simpleIntegerMap.UnwrapOr(map[]) == map["Test3" := 3];
        expect input.structureList.UnwrapOr([]) == [StructureListElement(stringValue := Some("Test2"), integerValue := Some(2))];
        expect input.nestedStructure.UnwrapOr(NestedStructure(stringStructure := Some(StringStructure(value := Some("")))))
            == NestedStructure(stringStructure := Some(StringStructure(value := Some("Nested"))));
    }
}