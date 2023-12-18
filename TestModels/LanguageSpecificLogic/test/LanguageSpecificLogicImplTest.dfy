// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

replaceable module LanguageSpecificLogicImplTest {
    import LanguageSpecificLogic
    import opened Wrappers
    import opened LanguageSpecificLogicTypes

    // Note that modules that `replace` this module will inherit tests in the `replaceable` module.
    // The tests in this file will run once in the context of the replaceable module (`LanguageSpecificLogicImplTest`)
    //   and once per replacing module.
    // Any tests in a `replaceable` module must be generic enough to apply to all languages.
    method{:test} AllLanguageTests() {
        var client :- expect LanguageSpecificLogic.LanguageSpecificLogic();
        TestAllLanguagesSuccess(client);
    }

    method TestAllLanguagesSuccess(client: ILanguageSpecificLogicClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()    
    {
        var output := client.GetRuntimeInformation();
        expect output.Success?;
        // Without knowing the language we are using, there isn't much to assert other than success...
        // However, we can still write a `print` which will apply to all runtimes:
        print"Generic language: ", output.value.language, "; Generic runtime: ", output.value.runtime;

    }
}
