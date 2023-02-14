include "../src/Index.dfy"

module SimpleConstraintsImplTest {
    import SimpleConstraints
    import StandardLibrary.UInt
    import opened SimpleConstraintsTypes
    import opened Wrappers
    method{:test} TestConstraints(){
        var client :- expect SimpleConstraints.SimpleConstraints();
        TestGetConstraintWithValidInputs(client);
    }

    method TestGetConstraintWithValidInputs(client: ISimpleConstraintsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var input := GetConstraintsInputTemplate();
      var ret := client.GetConstraints(input := input);
      expect ret.Success?;
    }

    // Example for overriding GetConstraintInputTemplate with an invalid input
    // 
    // method TestGetConstraintWithInvalidMyString(client: ISimpleConstraintsClient)
    //   requires client.ValidState()
    //   modifies client.Modifies
    //   ensures client.ValidState()
    // {
    //   var input := GetConstraintsInputTemplate(overrideToInvalidInput := {"myString"});
    //   var ret := client.GetConstraints(input := input);
    // }

    // TODO: Add invalid inputs after writing Dotnet constraint codegen
      
    // This returns a GetConstraintsInput object. 
    // By default with no parameters, this will return a valid GetConstraintsInput object.
    //   ("valid": Expected to pass Dafny predicate checks and runtime constraint validations.)
    // TODO: Passing in the name of a variable will override that variable to an invalid variable.
    //    ex. GetConstraintsInputTemplate("lessThanTen") could set "lessThanTen" equal to 14.
    method GetConstraintsInputTemplate(overrideToInvalidInput: set<string> := {})
      returns (output: GetConstraintsInput)
    {
      var overrideMyString: bool := "myString" in overrideToInvalidInput;
      var myString: MyString;
      if (overrideMyString) {
        myString := InvalidMyStringInput();
      } else {
        myString := "bw1and10";
      }

      var overrideNonEmptyString: bool := "nonEmptyString" in overrideToInvalidInput;
      var nonEmptyString: NonEmptyString;
      if (overrideNonEmptyString) {
        nonEmptyString := InvalidNonEmptyStringInput();
      } else {
        nonEmptyString := "atleast1";
      }

      var overrideStringLessThanOrEqualToTen: bool := "overrideStringLessThanOrEqualToTen" in overrideToInvalidInput;
      var stringLessThanOrEqualToTen: StringLessThanOrEqualToTen;
      if (overrideStringLessThanOrEqualToTen) {
        stringLessThanOrEqualToTen := InvalidStringLessThanOrEqualToTen();
      } else {
        stringLessThanOrEqualToTen := "leq10";
      }

      var overrideMyBlob: bool := "myBlob" in overrideToInvalidInput;
      var myBlob: MyBlob;
      if (overrideMyBlob) {
        myBlob := InvalidMyBlob();
      } else {
        myBlob := [0, 1, 0, 1]; 
      }

      // TODO: Write more overrides to invalid inputs below...

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

    method InvalidLessThanTenInput()
      returns (invalid: LessThanTen)
    {
      var invalidLessThanTenInput := 12;
      assume {:axiom} IsValid_LessThanTen(invalidLessThanTenInput);
      var invalidLessThanTen: LessThanTen := invalidLessThanTenInput;
      return invalidLessThanTen;
    }

    method InvalidMyStringInput()
      returns (invalid: MyString)
    {
      var invalidMyStringInput := "thisislongerthan10characters";
      assume {:axiom} IsValid_MyString(invalidMyStringInput);
      var invalidMyString: MyString := invalidMyStringInput;
      return invalidMyString;
    }

    method InvalidNonEmptyStringInput()
      returns (invalid: NonEmptyString)
    {
      var invalidNonEmptyStringInput := "";
      assume {:axiom} IsValid_NonEmptyString(invalidNonEmptyStringInput);
      var invalidNonEmptyString: NonEmptyString := invalidNonEmptyStringInput;
      return invalidNonEmptyString;
    }

    method InvalidStringLessThanOrEqualToTen()
      returns (invalid: StringLessThanOrEqualToTen)
    {
      var invalidStringLessThanOrEqualToTenInput := "";
      assume {:axiom} IsValid_StringLessThanOrEqualToTen(invalidStringLessThanOrEqualToTenInput);
      var invalidStringLessThanOrEqualToTen: StringLessThanOrEqualToTen := invalidStringLessThanOrEqualToTenInput;
      return invalidStringLessThanOrEqualToTen;
    }

    method InvalidMyBlob()
      returns (invalid: MyBlob)
    {
      var invalidMyBlobInput := []; // Invalid because |x| < 1; predicate requires 1 <= |x| <= 10
      assume {:axiom} IsValid_MyBlob(invalidMyBlobInput);
      var invalidMyBlob: MyBlob := invalidMyBlobInput;
      return invalidMyBlob;
    }

    // TODO: Write more invalid input generators...

}
