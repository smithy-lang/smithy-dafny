// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleRecursiveShapeImpl.dfy"
include "SimpleRecursiveShapeImplTest.dfy"

module WrappedSimpleTypesStringTest {
  import WrappedSimpleRecursiveShapeService
  import SimpleRecursiveShapeImplTest
  import opened Wrappers
  method{:test} GetRecursiveShape() {
    var client :- expect WrappedSimpleRecursiveShapeService.WrappedSimpleRecursiveShape();
    SimpleRecursiveShapeImplTest.TestGetRecursiveShape(client);
  }
}