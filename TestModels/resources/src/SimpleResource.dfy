// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"
include "./Config.dfy"

module SimpleResource {
  import opened StandardLibrary
  import opened Wrappers
  import opened Config    
  import Types = SimpleResourcesTypes    

  class SimpleResource extends Types.ISimpleResource
  {
    const config: Config

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
      && ModifiesInternalConfig(config) <= Modifies
      && History !in ModifiesInternalConfig(config)
      && ValidInternalConfig?(config)
    }

    const value: string

    constructor (
      value: string,
      config: Config
    )
      requires ValidInternalConfig?(config)
      ensures this.value == value
      ensures this.config == config
      ensures ValidState() && fresh(History) && fresh(Modifies - ModifiesInternalConfig(config))
    {
      this.value := value;
      this.config := config;

      History := new Types.ISimpleResourceCallHistory();
      Modifies := { History } + ModifiesInternalConfig(config);
    }

    predicate GetResourceDataEnsuresPublicly(
      input: Types.GetResourceDataInput,
      output: Result<Types.GetResourceDataOutput, Types.Error>
    ) {true}

    method GetResourceData'(
      input: Types.GetResourceDataInput
    ) returns (
      output: Result<Types.GetResourceDataOutput, Types.Error>
    )
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures && ValidState()
      ensures GetResourceDataEnsuresPublicly(input, output)
      ensures unchanged(History)
    {
      var rtnString: string := if input.stringValue.Some? then
        this.config.name + " " + input.stringValue.value
      else
        this.config.name;
      var rtn: Types.GetResourceDataOutput := Types.GetResourceDataOutput(
        blobValue := input.blobValue,
        booleanValue := input.booleanValue,
        stringValue := Option.Some(rtnString),
        integerValue := input.integerValue,
        longValue := input.longValue
      );
      return Success(rtn);  
    }
  }
}
