// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleRecursiveShapeTypesWrapped.dfy"

module WrappedSimpleRecursiveShapeService refines WrappedAbstractSimpleRecursiveShapeService {
  import WrappedService = SimpleRecursiveShape
  function method WrappedDefaultSimpleRecursiveShapeConfig(): SimpleRecursiveShapeConfig {
    SimpleRecursiveShapeConfig
  }
}
