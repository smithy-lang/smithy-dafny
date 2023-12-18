// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../../WrappedLanguageSpecificLogicImpl.dfy"

// Replaced in test/ directory
module {:extern "language.specific.logic.internaldafny.wrapped"} NetWrappedLanguageSpecificLogicService replaces WrappedLanguageSpecificLogicService {
}
