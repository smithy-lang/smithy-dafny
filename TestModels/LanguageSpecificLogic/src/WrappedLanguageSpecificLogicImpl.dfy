// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/LanguageSpecificLogicTypesWrapped.dfy"

module {:extern "language.specific.logic.internaldafny.wrapped"}
        WrappedLanguageSpecificLogicService refines WrappedAbstractLanguageSpecificLogicService {
    import WrappedService = LanguageSpecificLogic
    function method WrappedDefaultLanguageSpecificLogicConfig(): LanguageSpecificLogicConfig {
        WrappedService.DefaultLanguageSpecificLogicConfig()
    }
}
