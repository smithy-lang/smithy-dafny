// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDocumentationTypesWrapped.dfy"

module {:options "--function-syntax:4"} {:extern "simple.documentation.internaldafny.wrapped"} WrappedSimpleDocumentationService refines WrappedAbstractSimpleDocumentationService {
  import WrappedService = SimpleDocumentation
  function WrappedDefaultSimpleDocumentationConfig(): SimpleDocumentationConfig {
    SimpleDocumentationConfig
  }
}
