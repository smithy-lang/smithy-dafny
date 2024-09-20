// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../../../src/WrappedLanguageSpecificLogicImpl.dfy"
include "../../WrappedLanguageSpecificLogicImplTest.dfy"
include "LanguageSpecificLogicImplTest.dfy"

// Note that by replacing a `replaceable` module, this file will also run tests from that module.
module PythonWrappedLanguageSpecificLogicTest replaces WrappedLanguageSpecificLogicTest {
    import PythonLanguageSpecificLogicImplTest
    
    method{:test} WrappedPythonOnlyTests() {
        var client :- expect WrappedLanguageSpecificLogicService.WrappedLanguageSpecificLogic();
        PythonLanguageSpecificLogicImplTest.TestPythonClient(client);
    }
}
