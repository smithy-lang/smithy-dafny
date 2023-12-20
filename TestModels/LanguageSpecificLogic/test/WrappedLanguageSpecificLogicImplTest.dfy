// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedLanguageSpecificLogicImpl.dfy"
include "LanguageSpecificLogicImplTest.dfy"

replaceable module WrappedLanguageSpecificLogicTest {
    import WrappedLanguageSpecificLogicService
    import LanguageSpecificLogicImplTest
    import opened Wrappers
    
    // Note that modules that `replace` this module will inherit these tests.
    // The tests in this file will run multiple times:
    // - Once in the context of the replaceable module;
    // - Once once per replacing module.
    method{:test} WrappedAllLanguageTests() {
        var client :- expect WrappedLanguageSpecificLogicService.WrappedLanguageSpecificLogic();
        LanguageSpecificLogicImplTest.TestAllLanguagesSuccess(client);
    }
}
