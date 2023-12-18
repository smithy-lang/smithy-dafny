// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../../../src/WrappedLanguageSpecificLogicImpl.dfy"
include "../../WrappedLanguageSpecificLogicImplTest.dfy"
include "LanguageSpecificLogicImplTest.dfy"

// Note: We do NOT declare an extern here, but we DO declare a replaceable module.
// We only need language-specific behavior here, not language-specific externs. 
module NetWrappedLanguageSpecificLogicTest replaces WrappedLanguageSpecificLogicTest {
    import NetLanguageSpecificLogicImplTest
    
    method{:test} WrappedNetOnlyTests() {
        var client :- expect WrappedLanguageSpecificLogicService.WrappedLanguageSpecificLogic();
        NetLanguageSpecificLogicImplTest.TestNetClient(client);
    }
}
