// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesTimestampTypesWrapped.dfy"

module {:extern "simple.types.timestamp.internaldafny.wrapped"} WrappedSimpleTypesTimestampService refines WrappedAbstractSimpleTypesTimestampService {
  import WrappedService = SimpleTimestamp
  function method WrappedDefaultSimpleTimestampConfig(): SimpleTimestampConfig {
    SimpleTimestampConfig
  }
}
