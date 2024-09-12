// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleErrorsTypesWrapped.dfy"

module {:extern "simple.errors.internaldafny.wrapped"} WrappedSimpleErrorsService refines WrappedAbstractSimpleErrorsService {
    import WrappedService = SimpleErrors
    function method WrappedDefaultSimpleErrorsConfig(): SimpleErrorsConfig {
        SimpleErrorsConfig
    }
}
