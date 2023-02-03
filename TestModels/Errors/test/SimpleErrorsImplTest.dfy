include "../src/Index.dfy"

module SimpleErrorsImplTest {
    import SimpleErrors
    import StandardLibrary.UInt
    import opened SimpleErrorsTypes
    import opened Wrappers
    method{:test} GetErrors(){
        var client :- expect SimpleErrors.SimpleErrors();
        TestAlwaysError(client);
    }

    method TestAlwaysError(client: ISimpleErrorsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var e: string := "this is an error";
      var convertedErrorInput: GetErrorsInput := SimpleErrors.Types.GetErrorsInput(value := Some(e));

      var ret :- expect client.AlwaysError(convertedErrorInput);

      expect ret.value.UnwrapOr("") == e;
      print ret;
    }
}