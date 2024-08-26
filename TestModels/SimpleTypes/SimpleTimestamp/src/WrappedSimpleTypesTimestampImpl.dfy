// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesTimestampTypesWrapped.dfy"

module {:options "--function-syntax:4"} {:extern "simple.types.timestamp.internaldafny.wrapped"} WrappedSimpleTypesTimestampService refines WrappedAbstractSimpleTypesTimestampService {
  import WrappedService = SimpleTimestamp
  function WrappedDefaultSimpleTimestampConfig(): SimpleTimestampConfig {
    SimpleTimestampConfig
  }
}
