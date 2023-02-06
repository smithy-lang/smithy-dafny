include "../src/Index.dfy"

module SimpleErrorsImplTest {
    import SimpleErrors
    import StandardLibrary.UInt
    import opened SimpleErrorsTypes
    import opened Wrappers
    method{:test} TestErrors(){
        var client :- expect SimpleErrors.SimpleErrors();
        TestAlwaysError(client);
    }

    method TestAlwaysError(client: ISimpleErrorsClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var s: string := "this is an error";
      var e: Error := SimpleErrors.Types.SimpleErrorsException(message := s);
      var convertedErrorInput: AlwaysErrorInput := SimpleErrors.Types.AlwaysErrorInput(value := Some(e));

      var ret :- expect client.AlwaysError(convertedErrorInput);

      // ret.value is Option
      expect ret.value.Some?;
      // ret.value.value is Error
      expect ret.value.value == e;
      expect ret.value.value.SimpleErrorsException?;
      expect ret.value.value.message == s;
      print ret;
    }
}