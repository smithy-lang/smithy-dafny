include "../Model/SimpleResourcesTypes.dfy"

module SimpleResourcesImpl refines AbstractSimpleResourcesOperations {
  datatype Config = Config
  type InternalConfig = Config

  predicate ValidInternalConfig?(config: InternalConfig)
  {true}

  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}

  predicate GetResourcesEnsuresPublicly(
    input: GetResourcesInput,
    output: Result<GetResourcesOutput, Error>
  ) {true}

  method GetResources(
    config: InternalConfig,
    input: GetResourcesInput
  ) returns (output: Result<GetResourcesOutput, Error>)
  
  
}
