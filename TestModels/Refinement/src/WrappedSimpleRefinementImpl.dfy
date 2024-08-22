// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleRefinementTypesWrapped.dfy"

module {:extern "simple.refinement.internaldafny.wrapped"} WrappedSimpleRefinementService refines WrappedAbstractSimpleRefinementService {
    import WrappedService = SimpleRefinement
    function method WrappedDefaultSimpleRefinementConfig(): SimpleRefinementConfig {
        SimpleRefinementConfig
    }
}
