include "../src/Index.dfy"

module SimpleErrorsImplTest {
    import SimpleErrors
    import StandardLibrary.UInt
    import opened SimpleErrorsTypes
    import opened Wrappers
    method{:test} TestErrors(){
        var client :- expect SimpleErrors.SimpleErrors();
        TestAlwaysError(client);
        TestAlwaysMultipleErrors(client);
        TestAlwaysNativeError(client);
    }

    method TestAlwaysError(client: ISimpleErrorsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var s: string := "this is an error";
      var convertedErrorInput: GetErrorsInput := SimpleErrors.Types.GetErrorsInput(value := Some(s));

      var ret := client.AlwaysError(convertedErrorInput);
      print ret;

      expect ret.Failure?;
      expect ret.error == SimpleErrorsException(message := s);
    }

    method TestAlwaysMultipleErrors(client: ISimpleErrorsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      // This is commented out because Dotnet codegen does not support conversion to/from Dafny for Collection errors.
      // This should be uncommented out as part of adding Collection support, as this can be used to validate that the
      //   Collection conversion implementation works as expected.
      // TODO: Uncomment below as testing for Collection conversion
      // 
      // var s: string := "this is in a collection of errors";
      // var convertedErrorInput: GetErrorsInput := SimpleErrors.Types.GetErrorsInput(value := Some(s));

      // var ret := client.AlwaysMultipleErrors(convertedErrorInput);
      // print ret;

      // // TODO: Expect a Collection.
      // expect ret.Failure?;
      // expect ret.error.Collection?;

      // var expectedValue := Collection(list := [ SimpleErrorsException(message := s) ]);
      // expect ret.error == expectedValue;
    }

    method TestAlwaysNativeError(client: ISimpleErrorsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var s: string := "this will be a native/opaque error";
      var convertedErrorInput: GetErrorsInput := SimpleErrors.Types.GetErrorsInput(value := Some(s));

      var ret := client.AlwaysNativeError(convertedErrorInput);

      expect ret.Failure?;
      expect ret.error.Opaque?;
    }
}