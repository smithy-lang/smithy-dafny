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
      var s: string := "this is in multiple errors";
      var convertedErrorInput: GetErrorsInput := SimpleErrors.Types.GetErrorsInput(value := Some(s));

      var ret := client.AlwaysMultipleErrors(convertedErrorInput);
      print ret;

      // TODO: Expect a Collection.
      expect ret.Failure?;
      var expectedValueInsideCollection := SimpleErrorsException(message := s);
      expect ret.error == expectedValueInsideCollection;
    }

    method TestAlwaysNativeError(client: ISimpleErrorsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var s: string := "this will be a native/opaque error after SIM CrypTool-5085";
      var convertedErrorInput: GetErrorsInput := SimpleErrors.Types.GetErrorsInput(value := Some(s));

      var ret := client.AlwaysNativeError(convertedErrorInput);
      print ret;

      expect ret.Failure?;
      // TOOD: This should be a native/opaque error after SIM CrypTool-5085
      expect ret.error == SimpleErrorsException(message := s);
    }
}