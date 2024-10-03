// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "Index.dfy"

// Note that by replacing a `replaceable` module, this file will also run tests from that module.
module PythonLanguageSpecificLogicImplTest replaces LanguageSpecificLogicImplTest {

    method{:test} PythonSpecificTests() {
        var client :- expect LanguageSpecificLogic.LanguageSpecificLogic();
        TestPythonClient(client);
    }

    method TestPythonClient(client: ILanguageSpecificLogicClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var output := client.GetRuntimeInformation();
        expect output.Success?;
        // For Python-only tests, we can assert the output language is Python
        expect output.value.language == "Python";
        // We could also assert some result on the extern's result (i.e. runtime version), but won't

        // We should ONLY see printed values like "Python language: Python".
        // We should ALSO see printed values like "Generic language: Python" from the `replaceable` tests.
        print"Python language: ", output.value.language, "; Python runtime: ", output.value.runtime;
    }
}