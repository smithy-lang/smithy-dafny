// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

replaceable module LanguageSpecificLogicImplTest {
    import LanguageSpecificLogic
    import opened Wrappers
    import opened LanguageSpecificLogicTypes

    // Note that modules that `replace` this module will inherit these tests.
    // The tests in this file will run multiple times:
    // - Once in the context of the replaceable module;
    // - Once once per replacing module.
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
        // Any tests in a `replaceable` module must be generic enough to apply to all languages.
        // However, we can still write a `print` which will apply to all runtimes:
        print"Generic language: ", output.value.language, "; Generic runtime: ", output.value.runtime;
        // Checking the output demonstrates that each language is represented in a "Generic" print.
        // We can add language-specific prints to validate that each language also has its own print.
    }
}
