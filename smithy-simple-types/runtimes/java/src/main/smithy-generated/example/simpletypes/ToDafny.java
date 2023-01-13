// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package example.simpletypes;

import Dafny.Example.Simpletypes.Types.EmptyConfig;
import Dafny.Example.Simpletypes.Types.Error;
import Dafny.Example.Simpletypes.Types.GetStringInput;
import Dafny.Example.Simpletypes.Types.GetStringOutput;
import Wrappers_Compile.Option;
import dafny.DafnySequence;
import example.simpletypes.model.CollectionOfErrors;
import example.simpletypes.model.NativeError;
import example.simpletypes.model.OpaqueError;
import java.lang.Character;
import java.util.Objects;

public class ToDafny {
  public static Error Error(NativeError nativeValue) {
    if (nativeValue instanceof OpaqueError) {
      return ToDafny.Error((OpaqueError) nativeValue);
    }
    if (nativeValue instanceof CollectionOfErrors) {
      return ToDafny.Error((CollectionOfErrors) nativeValue);
    }
    return Error.create_Opaque(nativeValue);
  }

  public static Error Error(OpaqueError nativeValue) {
    return Error.create_Opaque(nativeValue.obj());
  }

  public static Error Error(CollectionOfErrors nativeValue) {
    DafnySequence<? extends Error> list = software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue.list(), 
        ToDafny::Error, 
        Error._typeDescriptor());
    return Error.create_Collection(list);
  }

  public static GetStringInput GetStringInput(
      example.simpletypes.model.GetStringInput nativeValue) {
    Option<DafnySequence<? extends Character>> stringValue;
    stringValue = Objects.nonNull(nativeValue.stringValue()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.stringValue()))
        : Option.create_None();
    return new GetStringInput(stringValue);
  }

  public static GetStringOutput GetStringOutput(
      example.simpletypes.model.GetStringOutput nativeValue) {
    Option<DafnySequence<? extends Character>> result;
    result = Objects.nonNull(nativeValue.result()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.result()))
        : Option.create_None();
    return new GetStringOutput(result);
  }

  public static EmptyConfig EmptyConfig(example.simpletypes.model.EmptyConfig nativeValue) {
    return new EmptyConfig();
  }
}
