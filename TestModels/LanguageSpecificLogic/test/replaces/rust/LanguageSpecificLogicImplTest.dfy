// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "Index.dfy"

// Note that by replacing a `replaceable` module, this file will also run tests from that module.
module RustLanguageSpecificLogicImplTest replaces LanguageSpecificLogicImplTest {

    method {:test} RustSpecificTests() {
        var client :- expect LanguageSpecificLogic.LanguageSpecificLogic();
        TestRustClient(client);
    }

    method TestRustClient(client: ILanguageSpecificLogicClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var output := client.GetRuntimeInformation();
        expect output.Success?;
        // For Rust-only tests, we can assert the output language is Rust
        expect output.value.language == "Rust";
        // We could also assert some result on the extern's result (i.e. runtime version), but won't

        // We should ONLY see printed values like "Rust language: Rust".
        // We should ALSO see printed values like "Generic language: Rust" from the `replaceable` tests.
        print "Rust language: ", output.value.language, "; Rust runtime: ", output.value.runtime, "\n";
    }
}
