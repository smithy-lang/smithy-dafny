include "../Model/SimpleTypesEnumTypes.dfy"

module SimpleEnumImpl refines AbstractSimpleTypesEnumOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
   predicate GetEnumEnsuresPublicly(input: GetEnumInput, output: Result<GetEnumOutput, Error>) {
    true
   }
 method GetEnum ( config: InternalConfig,  input: GetEnumInput )
 returns (output: Result<GetEnumOutput, Error>) {
    var res := GetEnumOutput(value := input.value);
    return Success(res);
 }
}