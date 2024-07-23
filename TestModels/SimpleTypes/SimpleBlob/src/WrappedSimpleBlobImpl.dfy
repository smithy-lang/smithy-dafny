// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesBlobTypesWrapped.dfy"

module WrappedSimpleTypesBlobService refines WrappedAbstractSimpleTypesBlobService {
    import WrappedService = SimpleBlob
    function method WrappedDefaultSimpleBlobConfig(): SimpleBlobConfig {
        SimpleBlobConfig
    }
}
