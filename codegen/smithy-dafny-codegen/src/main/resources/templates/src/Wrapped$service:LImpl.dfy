// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/$service:LTypesWrapped.dfy"

module {:options "--function-syntax:4"} {:extern "$namespace:L.internaldafny.wrapped"} Wrapped$service:LService refines WrappedAbstract$service:LService {
    import WrappedService = $sdkID:L
    function WrappedDefault$serviceConfig:L(): $serviceConfig:L {
        $serviceConfig:L
    }
}
