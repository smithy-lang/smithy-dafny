include "Index.dfy"

module NetLanguageSpecificLogicImplTest replaces LanguageSpecificLogicImplTest {
    import NetLanguageSpecificLogic

    method{:test} NetSpecificTests() {
        var client :- expect NetLanguageSpecificLogic.LanguageSpecificLogic();
        TestNetClient(client);
    }

    method TestNetClient(client: ILanguageSpecificLogicClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var output := client.GetRuntimeInformation();
        expect output.Success?;
        // For NET-only tests, we can assert the output language is NET
        expect output.value.language == "NET";
        // We could also assert some result on the extern's result (i.e. runtime version)
        print"NET language: ", output.value.language, "; NET runtime: ", output.value.runtime;
    }
}