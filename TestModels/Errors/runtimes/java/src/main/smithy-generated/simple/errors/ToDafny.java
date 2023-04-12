// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.errors;

import Dafny.Simple.Errors.Types.Error;
import Dafny.Simple.Errors.Types.Error_SimpleErrorsException;
import Dafny.Simple.Errors.Types.GetErrorsInput;
import Dafny.Simple.Errors.Types.GetErrorsOutput;
import Dafny.Simple.Errors.Types.SimpleErrorsConfig;
import Wrappers_Compile.Option;
import dafny.DafnySequence;
import java.lang.Character;
import java.util.Objects;
import simple.errors.model.CollectionOfErrors;
import simple.errors.model.NativeError;
import simple.errors.model.OpaqueError;
import simple.errors.model.SimpleErrorsException;

public class ToDafny {
  public static Error Error(NativeError nativeValue) {
    if (nativeValue instanceof SimpleErrorsException) {
      return ToDafny.Error((SimpleErrorsException) nativeValue);
    }
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
    return Error.create_CollectionOfErrors(list);
  }

  public static GetErrorsInput GetErrorsInput(simple.errors.model.GetErrorsInput nativeValue) {
    Option<DafnySequence<? extends Character>> value;
    value = Objects.nonNull(nativeValue.value()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.value()))
        : Option.create_None();
    return new GetErrorsInput(value);
  }

  public static SimpleErrorsConfig SimpleErrorsConfig(
      simple.errors.model.SimpleErrorsConfig nativeValue) {
    return new SimpleErrorsConfig();
  }

  public static GetErrorsOutput GetErrorsOutput(simple.errors.model.GetErrorsOutput nativeValue) {
    Option<DafnySequence<? extends Character>> value;
    value = Objects.nonNull(nativeValue.value()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.value()))
        : Option.create_None();
    return new GetErrorsOutput(value);
  }

  public static Error Error(SimpleErrorsException nativeValue) {
    DafnySequence<? extends Character> message;
    message = software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.message());
    return new Error_SimpleErrorsException(message);
  }
}
