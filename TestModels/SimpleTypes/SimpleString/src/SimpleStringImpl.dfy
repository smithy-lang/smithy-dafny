include "../Model/SimpleTypesStringTypes.dfy"

module SimpleStringImpl refines AbstractSimpleTypesStringOperations  {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>) {
        true
    }
    predicate GetStringSingleValueEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>) {
        true
    }
    predicate GetStringUTF8EnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>) {
        true
    }
    method GetString ( config: InternalConfig,  input: GetStringInput )
    returns (output: Result<GetStringOutput, Error>) {
        var res := GetStringOutput(value := input.value);
        return Success(res);
    }
    method GetStringSingleValue ( config: InternalConfig,  input: GetStringInput )
    returns (output: Result<GetStringOutput, Error>) {
        expect input.value.Some?;
        expect input.value.value == "TEST_SIMPLE_STRING_SINGLE_VALUE"; // This is done so as to assert that polymorph layer is doing one way conversion right as well.
        var res := GetStringOutput(value := input.value);
        return Success(res);
    }
    method GetStringUTF8 ( config: InternalConfig,  input: GetStringInput )
    returns (output: Result<GetStringOutput, Error>) {
        expect input.value.Some?;
        var res := GetStringOutput(value := input.value);
        return Success(res);
    }
}