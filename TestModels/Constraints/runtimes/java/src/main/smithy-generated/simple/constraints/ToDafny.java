// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.constraints;

import Dafny.Simple.Constraints.Types.ComplexListElement;
import Dafny.Simple.Constraints.Types.Error;
import Dafny.Simple.Constraints.Types.GetConstraintsInput;
import Dafny.Simple.Constraints.Types.GetConstraintsOutput;
import Dafny.Simple.Constraints.Types.SimpleConstraintsConfig;
import Wrappers_Compile.Option;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.TypeDescriptor;
import java.lang.Byte;
import java.lang.Character;
import java.lang.Integer;
import java.lang.String;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import simple.constraints.model.CollectionOfErrors;
import simple.constraints.model.NativeError;
import simple.constraints.model.OpaqueError;

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
    return Error.create_CollectionOfErrors(list);
  }

  public static SimpleConstraintsConfig SimpleConstraintsConfig(
      simple.constraints.model.SimpleConstraintsConfig nativeValue) {
    return new SimpleConstraintsConfig();
  }

  public static ComplexListElement ComplexListElement(
      simple.constraints.model.ComplexListElement nativeValue) {
    Option<DafnySequence<? extends Character>> value;
    value = Objects.nonNull(nativeValue.value()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.value()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> blob;
    blob = Objects.nonNull(nativeValue.blob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.blob()))
        : Option.create_None();
    return new ComplexListElement(value, blob);
  }

  public static GetConstraintsInput GetConstraintsInput(
      simple.constraints.model.GetConstraintsInput nativeValue) {
    Option<DafnySequence<? extends Character>> myString;
    myString = Objects.nonNull(nativeValue.MyString()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.MyString()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> nonEmptyString;
    nonEmptyString = Objects.nonNull(nativeValue.NonEmptyString()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.NonEmptyString()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> stringLessThanOrEqualToTen;
    stringLessThanOrEqualToTen = Objects.nonNull(nativeValue.StringLessThanOrEqualToTen()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.StringLessThanOrEqualToTen()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> myBlob;
    myBlob = Objects.nonNull(nativeValue.MyBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.MyBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> nonEmptyBlob;
    nonEmptyBlob = Objects.nonNull(nativeValue.NonEmptyBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.NonEmptyBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> blobLessThanOrEqualToTen;
    blobLessThanOrEqualToTen = Objects.nonNull(nativeValue.BlobLessThanOrEqualToTen()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.BlobLessThanOrEqualToTen()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> myList;
    myList = (Objects.nonNull(nativeValue.MyList()) && nativeValue.MyList().size() > 0) ?
        Option.create_Some(ToDafny.MyList(nativeValue.MyList()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> nonEmptyList;
    nonEmptyList = (Objects.nonNull(nativeValue.NonEmptyList()) && nativeValue.NonEmptyList().size() > 0) ?
        Option.create_Some(ToDafny.NonEmptyList(nativeValue.NonEmptyList()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> listLessThanOrEqualToTen;
    listLessThanOrEqualToTen = (Objects.nonNull(nativeValue.ListLessThanOrEqualToTen()) && nativeValue.ListLessThanOrEqualToTen().size() > 0) ?
        Option.create_Some(ToDafny.ListLessThanOrEqualToTen(nativeValue.ListLessThanOrEqualToTen()))
        : Option.create_None();
    Option<DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>>> myMap;
    myMap = (Objects.nonNull(nativeValue.MyMap()) && nativeValue.MyMap().size() > 0) ?
        Option.create_Some(ToDafny.MyMap(nativeValue.MyMap()))
        : Option.create_None();
    Option<DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>>> nonEmptyMap;
    nonEmptyMap = (Objects.nonNull(nativeValue.NonEmptyMap()) && nativeValue.NonEmptyMap().size() > 0) ?
        Option.create_Some(ToDafny.NonEmptyMap(nativeValue.NonEmptyMap()))
        : Option.create_None();
    Option<DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>>> mapLessThanOrEqualToTen;
    mapLessThanOrEqualToTen = (Objects.nonNull(nativeValue.MapLessThanOrEqualToTen()) && nativeValue.MapLessThanOrEqualToTen().size() > 0) ?
        Option.create_Some(ToDafny.MapLessThanOrEqualToTen(nativeValue.MapLessThanOrEqualToTen()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> alphabetic;
    alphabetic = Objects.nonNull(nativeValue.Alphabetic()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.Alphabetic()))
        : Option.create_None();
    Option<Integer> oneToTen;
    oneToTen = Objects.nonNull(nativeValue.OneToTen()) ?
        Option.create_Some((nativeValue.OneToTen()))
        : Option.create_None();
    Option<Integer> greaterThanOne;
    greaterThanOne = Objects.nonNull(nativeValue.GreaterThanOne()) ?
        Option.create_Some((nativeValue.GreaterThanOne()))
        : Option.create_None();
    Option<Integer> lessThanTen;
    lessThanTen = Objects.nonNull(nativeValue.LessThanTen()) ?
        Option.create_Some((nativeValue.LessThanTen()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> myUniqueList;
    myUniqueList = (Objects.nonNull(nativeValue.MyUniqueList()) && nativeValue.MyUniqueList().size() > 0) ?
        Option.create_Some(ToDafny.MyUniqueList(nativeValue.MyUniqueList()))
        : Option.create_None();
    Option<DafnySequence<? extends ComplexListElement>> myComplexUniqueList;
    myComplexUniqueList = (Objects.nonNull(nativeValue.MyComplexUniqueList()) && nativeValue.MyComplexUniqueList().size() > 0) ?
        Option.create_Some(ToDafny.MyComplexUniqueList(nativeValue.MyComplexUniqueList()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> myUtf8Bytes;
    myUtf8Bytes = Objects.nonNull(nativeValue.MyUtf8Bytes()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(nativeValue.MyUtf8Bytes()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Byte>>> myListOfUtf8Bytes;
    myListOfUtf8Bytes = (Objects.nonNull(nativeValue.MyListOfUtf8Bytes()) && nativeValue.MyListOfUtf8Bytes().size() > 0) ?
        Option.create_Some(ToDafny.ListOfUtf8Bytes(nativeValue.MyListOfUtf8Bytes()))
        : Option.create_None();
    return new GetConstraintsInput(myString, nonEmptyString, stringLessThanOrEqualToTen, myBlob, nonEmptyBlob, blobLessThanOrEqualToTen, myList, nonEmptyList, listLessThanOrEqualToTen, myMap, nonEmptyMap, mapLessThanOrEqualToTen, alphabetic, oneToTen, greaterThanOne, lessThanTen, myUniqueList, myComplexUniqueList, myUtf8Bytes, myListOfUtf8Bytes);
  }

  public static GetConstraintsOutput GetConstraintsOutput(
      simple.constraints.model.GetConstraintsOutput nativeValue) {
    Option<DafnySequence<? extends Character>> myString;
    myString = Objects.nonNull(nativeValue.MyString()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.MyString()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> nonEmptyString;
    nonEmptyString = Objects.nonNull(nativeValue.NonEmptyString()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.NonEmptyString()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> stringLessThanOrEqualToTen;
    stringLessThanOrEqualToTen = Objects.nonNull(nativeValue.StringLessThanOrEqualToTen()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.StringLessThanOrEqualToTen()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> myBlob;
    myBlob = Objects.nonNull(nativeValue.MyBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.MyBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> nonEmptyBlob;
    nonEmptyBlob = Objects.nonNull(nativeValue.NonEmptyBlob()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.NonEmptyBlob()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> blobLessThanOrEqualToTen;
    blobLessThanOrEqualToTen = Objects.nonNull(nativeValue.BlobLessThanOrEqualToTen()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.ByteSequence(nativeValue.BlobLessThanOrEqualToTen()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> myList;
    myList = (Objects.nonNull(nativeValue.MyList()) && nativeValue.MyList().size() > 0) ?
        Option.create_Some(ToDafny.MyList(nativeValue.MyList()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> nonEmptyList;
    nonEmptyList = (Objects.nonNull(nativeValue.NonEmptyList()) && nativeValue.NonEmptyList().size() > 0) ?
        Option.create_Some(ToDafny.NonEmptyList(nativeValue.NonEmptyList()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> listLessThanOrEqualToTen;
    listLessThanOrEqualToTen = (Objects.nonNull(nativeValue.ListLessThanOrEqualToTen()) && nativeValue.ListLessThanOrEqualToTen().size() > 0) ?
        Option.create_Some(ToDafny.ListLessThanOrEqualToTen(nativeValue.ListLessThanOrEqualToTen()))
        : Option.create_None();
    Option<DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>>> myMap;
    myMap = (Objects.nonNull(nativeValue.MyMap()) && nativeValue.MyMap().size() > 0) ?
        Option.create_Some(ToDafny.MyMap(nativeValue.MyMap()))
        : Option.create_None();
    Option<DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>>> nonEmptyMap;
    nonEmptyMap = (Objects.nonNull(nativeValue.NonEmptyMap()) && nativeValue.NonEmptyMap().size() > 0) ?
        Option.create_Some(ToDafny.NonEmptyMap(nativeValue.NonEmptyMap()))
        : Option.create_None();
    Option<DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>>> mapLessThanOrEqualToTen;
    mapLessThanOrEqualToTen = (Objects.nonNull(nativeValue.MapLessThanOrEqualToTen()) && nativeValue.MapLessThanOrEqualToTen().size() > 0) ?
        Option.create_Some(ToDafny.MapLessThanOrEqualToTen(nativeValue.MapLessThanOrEqualToTen()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> alphabetic;
    alphabetic = Objects.nonNull(nativeValue.Alphabetic()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.Alphabetic()))
        : Option.create_None();
    Option<Integer> oneToTen;
    oneToTen = Objects.nonNull(nativeValue.OneToTen()) ?
        Option.create_Some((nativeValue.OneToTen()))
        : Option.create_None();
    Option<Integer> greaterThanOne;
    greaterThanOne = Objects.nonNull(nativeValue.GreaterThanOne()) ?
        Option.create_Some((nativeValue.GreaterThanOne()))
        : Option.create_None();
    Option<Integer> lessThanTen;
    lessThanTen = Objects.nonNull(nativeValue.LessThanTen()) ?
        Option.create_Some((nativeValue.LessThanTen()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> myUniqueList;
    myUniqueList = (Objects.nonNull(nativeValue.MyUniqueList()) && nativeValue.MyUniqueList().size() > 0) ?
        Option.create_Some(ToDafny.MyUniqueList(nativeValue.MyUniqueList()))
        : Option.create_None();
    Option<DafnySequence<? extends ComplexListElement>> myComplexUniqueList;
    myComplexUniqueList = (Objects.nonNull(nativeValue.MyComplexUniqueList()) && nativeValue.MyComplexUniqueList().size() > 0) ?
        Option.create_Some(ToDafny.MyComplexUniqueList(nativeValue.MyComplexUniqueList()))
        : Option.create_None();
    Option<DafnySequence<? extends Byte>> myUtf8Bytes;
    myUtf8Bytes = Objects.nonNull(nativeValue.MyUtf8Bytes()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(nativeValue.MyUtf8Bytes()))
        : Option.create_None();
    Option<DafnySequence<? extends DafnySequence<? extends Byte>>> myListOfUtf8Bytes;
    myListOfUtf8Bytes = (Objects.nonNull(nativeValue.MyListOfUtf8Bytes()) && nativeValue.MyListOfUtf8Bytes().size() > 0) ?
        Option.create_Some(ToDafny.ListOfUtf8Bytes(nativeValue.MyListOfUtf8Bytes()))
        : Option.create_None();
    return new GetConstraintsOutput(myString, nonEmptyString, stringLessThanOrEqualToTen, myBlob, nonEmptyBlob, blobLessThanOrEqualToTen, myList, nonEmptyList, listLessThanOrEqualToTen, myMap, nonEmptyMap, mapLessThanOrEqualToTen, alphabetic, oneToTen, greaterThanOne, lessThanTen, myUniqueList, myComplexUniqueList, myUtf8Bytes, myListOfUtf8Bytes);
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> MyUniqueList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> ListLessThanOrEqualToTen(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> MyList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends DafnySequence<? extends Byte>> ListOfUtf8Bytes(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes, 
        DafnySequence._typeDescriptor(TypeDescriptor.BYTE));
  }

  public static DafnySequence<? extends DafnySequence<? extends Character>> NonEmptyList(
      List<String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
  }

  public static DafnySequence<? extends ComplexListElement> MyComplexUniqueList(
      List<simple.constraints.model.ComplexListElement> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue, 
        simple.constraints.ToDafny::ComplexListElement, 
        ComplexListElement._typeDescriptor());
  }

  public static DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>> MapLessThanOrEqualToTen(
      Map<String, String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToMap(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence);
  }

  public static DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>> NonEmptyMap(
      Map<String, String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToMap(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence);
  }

  public static DafnyMap<? extends DafnySequence<? extends Character>, ? extends DafnySequence<? extends Character>> MyMap(
      Map<String, String> nativeValue) {
    return software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToMap(
        nativeValue, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence, 
        software.amazon.dafny.conversion.ToDafny.Simple::CharacterSequence);
  }
}
