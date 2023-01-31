include "../Model/SimpleTypesBlobTypes.dfy"

module SimpleBlobImpl refines AbstractSimpleTypesBlobOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
   predicate GetBlobEnsuresPublicly(input: GetBlobInput, output: Result<GetBlobOutput, Error>) {
    true
   }
 method GetBlob ( config: InternalConfig,  input: GetBlobInput )
 returns (output: Result<GetBlobOutput, Error>) {
    expect input.value.Some?;

    // Validate seq<uint8> type properties on input
    // Input can contain items: "input has a measurable length of at least 0"
    expect |input.value.value| >= 0;
    // If input has at least one item, then:

    // Validate uint8 type properties on input values
    for i := 0 to |input.value.value| {
      // Input is index-accessible, which means input is seq-like rather than a set
      var inputElement := input.value.value[i];
      // "Input can be interpreted as any valid uint8"
      expect inputElement >= 0x0 || inputElement < 0x0;
    }

    // We have validated "input is a seq-like type containing elements that can be read as uint8s"
    // If input has 0 items, we don't care about validating properties on nonexistent items

    var res := GetBlobOutput(value := input.value);

    expect res.value.Some?;

    // Validate seq<uint8> type properties on input
    // Input can contain items: "input has a measurable length of at least 0"
    expect |res.value.value| >= 0;
    // If input has at least one item, then:

    // Validate uint8 type properties on input values
    for i := 0 to |res.value.value| {
      // Input is index-accessible, which means input is seq-like rather than a set
      var resElement := res.value.value[i];
      // "Input can be interpreted as any valid uint8"
      expect resElement >= 0x0 || resElement < 0x0;
    }
    
    // We have validated "res is a seq-like type containing elements that can be read as uint8s"

    // Validate values: input is the same as the output
    expect res.value.value == input.value.value;

    return Success(res);
 }
}