include "../src/Index.dfy"

module SimpleConstraintsImplTest {
    import SimpleConstraints
    import StandardLibrary.UInt
    import opened SimpleConstraintsTypes
    import opened Wrappers
    method{:test} TestConstraints(){
        var client :- expect SimpleConstraints.SimpleConstraints();
        TestGetConstraint(client);
    }

    method TestGetConstraint(client: ISimpleConstraintsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var input := GetConstraintsInputTemplate();
      var ret := client.GetConstraints(input := input);
      expect ret.Success?;
    }

    method TestGetConstraintWithInvalidMyString(client: ISimpleConstraintsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var input := GetConstraintsInputTemplate(overrideToInvalid := {"myString"});
      var ret := client.GetConstraints(input := input);
      expect ret.Success?;
    }
      
    // This returns a GetConstraintsInput object. 
    // By default with no parameters, this will return a valid GetConstraintsInput object.
    //   ("valid": Expected to pass Dafny predicate checks and runtime constraint validations.)
    // TODO: Passing in the name of a variable will override that variable to an invalid variable.
    //    ex. GetConstraintsInputTemplate("lessThanTen") could set "lessThanTen" equal to 14.
    method GetConstraintsInputTemplate(overrideToInvalid: set<string> := {})
      returns (output: GetConstraintsInput)
    {
      // TODO: Pass invalid constraint to runtime.
      // Context: We cannot pass an invalid input to GetConstraintsInput in Dafny.
      //    ex. Passing `lessThanTen := 14` is an invalid input as it violates the predicate `x < 10`.
      // If this is passed, Dafny will not transpile the test to a runtime as the code contains errors.
      // 
      // However, we may actually want to pass an invalid constraint into this input to test Polymorph.
      // Polymorph will generate a constraint validation function for constraint traits in Smithy models.
      // We would like to test this constraint validation function:
      //  - Passing "expected-valid" input results in Success
      //      (i.e. runtime constraint validation function did not error)
      //  - Passing "expected-invalid" input results in Failure
      //      (i.e. runtime constraint validation function threw error)
      // The easiest way to do create this test is to write it in Dafny, then transpile the test to a runtime.
      // However, since GetConstraintsInput will not accept an "expected-invalid" input, this isn't possible.
      //
      // A workaround is to add this line `assume {:axiom} false;`.
      // This will tell the Dafny compiler to ignore predicates for this function; however, the Polymorph compiler has
      //   already generated the corresponding runtime constraint validation function.
      // This allows us to test an "expected-invalid" input to GetConstraintsInput. The Dafny compiler will not error
      //   because the predicate is ignored, but the runtime constraint validation function will error because the
      //   input violates the constraints.
      // assume {:axiom} false;
      var myString := "bw1and10";
      var nonEmptyString := "atleast1";
      var stringLessThanOrEqualToTen := "leq10";
      var myBlob := [0, 1, 0, 1]; 
      var nonEmptyBlob := [0, 1, 0, 1]; 
      var BlobLessThanOrEqualToTen := [0, 1, 0, 1]; 
      var myList := ["00", "11"];
      var nonEmptyList := ["00", "11"];
      var listLessThanOrEqualToTen := ["00", "11"];
      var myMap := map["0" := "1", "2" := "3"];
      var nonEmptyMap := map["0" := "1", "2" := "3"];
      var mapLessThanOrEqualToTen := map["0" := "1", "2" := "3"];
      var alphabetic := "alphabetic";
      var oneToTen := 3;
      var greaterThanOne := 2;
      var lessThanTen := 3;
      var myUniqueList := ["one", "two"];
      var myComplexUniqueList := [ ComplexListElement(value := Some("one"), blob := Some([1, 1])),
                                   ComplexListElement(value := Some("two"), blob := Some([2, 2]))
                                 ];

      var input := GetConstraintsInput(
        MyString := Some(myString),
        NonEmptyString := Some(nonEmptyString),
        StringLessThanOrEqualToTen := Some(stringLessThanOrEqualToTen),
        MyBlob := Some(myBlob),
        NonEmptyBlob := Some(nonEmptyBlob),
        BlobLessThanOrEqualToTen := Some(BlobLessThanOrEqualToTen),
        MyList := Some(myList),
        NonEmptyList := Some(nonEmptyList),
        ListLessThanOrEqualToTen := Some(listLessThanOrEqualToTen),
        MyMap := Some(myMap),
        NonEmptyMap := Some(nonEmptyMap),
        MapLessThanOrEqualToTen := Some(mapLessThanOrEqualToTen),
        Alphabetic := Some(alphabetic),
        OneToTen := Some(oneToTen),
        GreaterThanOne := Some(greaterThanOne),
        LessThanTen := Some(lessThanTen),
        MyUniqueList := Some(myUniqueList),
        MyComplexUniqueList := Some(myComplexUniqueList)
      );

      return input;
    }
}
