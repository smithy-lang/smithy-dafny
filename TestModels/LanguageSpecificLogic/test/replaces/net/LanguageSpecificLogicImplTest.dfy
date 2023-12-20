// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "Index.dfy"

// Note that by replacing a `replaceable` module, this file will also run tests from that module.
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

        // We should ONLY see printed values like "NET language: NET".
        // We should ALSO see printed values like "Generic language: NET" from the `replaceable` tests.
        print"NET language: ", output.value.language, "; NET runtime: ", output.value.runtime;
    }
}