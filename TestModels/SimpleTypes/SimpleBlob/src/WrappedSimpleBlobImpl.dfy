// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesBlobTypesWrapped.dfy"

module {:extern "simple.types.blob.internaldafny.wrapped"} WrappedSimpleTypesBlobService refines WrappedAbstractSimpleTypesBlobService {
    import WrappedService = SimpleBlob
    function method WrappedDefaultSimpleBlobConfig(): SimpleBlobConfig {
        SimpleBlobConfig
    }
}
