// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../libraries/src/Wrappers.dfy"

//
// Helper functions for extern code to call in order to create common wrapper types.
// Currently necessary to abstract away from differences in TypeDescriptor usage
// in the Java backend across different versions of Dafny,
// but may be useful for other target languages in the future as well.
//
module StandardLibrary.Interop {

  import opened Wrappers

  class WrappersInterop {

    static function method CreateStringSome(s: string): Option<string> {
      Some(s)
    }

    static function method CreateStringNone(): Option<string> {
      None
    }

    static function method CreateBooleanSome(b: bool): Option<bool> {
      Some(b)
    }

    static function method CreateBooleanNone(): Option<bool> {
      None
    }
  }
}