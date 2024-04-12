// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../libraries/src/Wrappers.dfy"

//
// Helper functions for extern code to call in order to create common wrapper types.
//
// This is currently necessary to abstract away from differences in TypeDescriptor usage
// in the Java backend across different versions of Dafny:
// after Dafny 4.2 methods like Option.create_Some()
// also require explicit TypeDescriptor arguments.
// If we declare a `CreateSome<T>(t: T)` function,
// the compiled version may or may not need a type descriptor,
// which means test models would need to have different Java code for different Dafny versions.
// But if we define a non-generic version for a specific type,
// Dafny will emit the right type descriptor instances inside the compiled method,
// so the calling signature is the same across Dafny versions.
//
// These may be useful for other target languages in the future as well,
// to similarly abstract away from Dafny compilation internal details.
//
// See also DafnyApiCodegen.generateResultOfClientHelperFunctions(),
// which solves the same problem by emitting similar helper methods for each client type.
//
module StandardLibraryInterop {

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