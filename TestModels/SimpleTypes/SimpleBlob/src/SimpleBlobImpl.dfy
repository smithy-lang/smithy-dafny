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
  predicate GetBlobKnownValueTestEnsuresPublicly(input: GetBlobInput, output: Result<GetBlobOutput, Error>) {
    true
  }
  method GetBlob ( config: InternalConfig,  input: GetBlobInput )
    returns (output: Result<GetBlobOutput, Error>)
  {
    expect input.value.Some?;
    ValidateBlobType(input.value.value);

    var res := GetBlobOutput(value := input.value);
    expect res.value.Some?;
    ValidateBlobType(res.value.value);

    // Validate values: input is the same as the output
    expect res.value.value == input.value.value;

    return Success(res);
  }

  // This method is only used for known-value testing. See comment inside method which explains this method's purpose.
  method GetBlobKnownValueTest ( config: InternalConfig,  input: GetBlobInput )
    returns (output: Result<GetBlobOutput, Error>)
  {
    expect input.value.Some?;
    ValidateBlobType(input.value.value);

    // Known value test.
    //
    // The `input` variable this function was called with is not necessarily the same `input` that is referenced
    //   within this function.
    // ex. The transpiled code may have copied `input` by value into this function, rather than passing it by
    //   reference. This is runtime-dependent behavior. 
    // We cannot test the value of `input` from outside this function; it must be tested inside the 
    //   implementation. In the example above, if the copy-by-value is incorrect, we would not know by
    // 
    // However, in order to validate the value of `input` from within this function, we must test against a known Dafny
    //   value. This value cannot be passed into the function. As in the example above, this known value may also be
    //   copied by value, and potentially suffer the same mutations described above.
    // To validate this, we require a unique test vector that is defined in this function. This method is used in
    //   conjunction with a single test that always passes in [0x0, 0x2, 0x4]. As a result, this `expect` validates
    //   that the `input` referenced within this function matches the expected Dafny-defined test vector.
    //
    // Other than this `expect` statement, this function is the same as `GetBlob`.
    expect input.value.value == [0x0, 0x2, 0x4];

    var res := GetBlobOutput(value := input.value);
    expect res.value.Some?;
    ValidateBlobType(res.value.value);

    // Validate values: input is the same as the output
    expect res.value.value == input.value.value;

    return Success(res);
 }


 method ValidateBlobType(input: seq<UInt.uint8>)
 {
    // Validate seq<uint8> type properties on input
    // Input can contain items: "input has a measurable length of at least 0"
    expect |input| >= 0;

    // Validate uint8 type properties on input values
    for i := 0 to |input| {
      // Input is index-accessible, which means input is seq-like rather than a set
      var inputElement := input[i];
      // "Input can be interpreted as any valid uint8"
      expect inputElement >= 0x0;
    }
    // If input does not contain any values, we aren't interested in validating per-element properties on it
  }
}