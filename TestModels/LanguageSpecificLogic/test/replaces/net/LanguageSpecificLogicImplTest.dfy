include "Index.dfy"

// A nuance of replacing a `replaceable` module that has tests:
// Tests in the `replaceable` module will run once in the context of the replaceable module,
//   then again in the context of the replacing module.
module NetLanguageSpecificLogicImplTest replaces LanguageSpecificLogicImplTest {

    method{:test} NetSpecificTests() {
        var client :- expect LanguageSpecificLogic.LanguageSpecificLogic();
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
        // We could also assert some result on the extern's result (i.e. runtime version), but won't
        print"NET language: ", output.value.language, "; NET runtime: ", output.value.runtime;
    }
}