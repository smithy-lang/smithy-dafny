include "../Model/SimpleTypesBooleanTypes.dfy"

module SimpleBooleanImpl refines AbstractSimpleTypesBooleanOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
   predicate GetBooleanEnsuresPublicly(input: GetBooleanInput, output: Result<GetBooleanOutput, Error>) {
    true
   }
 method GetBoolean ( config: InternalConfig,  input: GetBooleanInput )
 returns (output: Result<GetBooleanOutput, Error>) {
    var res := GetBooleanOutput(value := input.value);
    return Success(res);
 }
}