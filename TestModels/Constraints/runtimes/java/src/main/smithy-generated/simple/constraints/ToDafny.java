// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.constraints;

import Wrappers_Compile.Option;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.TypeDescriptor;
import java.lang.Byte;
import java.lang.Character;
import java.lang.Integer;
import java.lang.Long;
import java.lang.RuntimeException;
import java.lang.String;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import simple.constraints.internaldafny.types.Error;
import simple.constraints.internaldafny.types.Error_SimpleConstraintsException;
import simple.constraints.internaldafny.types.GetConstraintsInput;
import simple.constraints.internaldafny.types.GetConstraintsOutput;
import simple.constraints.internaldafny.types.ISimpleConstraintsClient;
import simple.constraints.internaldafny.types.SimpleConstraintsConfig;
import simple.constraints.model.CollectionOfErrors;
import simple.constraints.model.OpaqueError;
import simple.constraints.model.SimpleConstraintsException;

public class ToDafny {

  public static Error Error(RuntimeException nativeValue) {
    if (nativeValue instanceof SimpleConstraintsException) {
      return ToDafny.Error((SimpleConstraintsException) nativeValue);
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
    DafnySequence<? extends Error> list =
      software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue.list(),
        ToDafny::Error,
        Error._typeDescriptor()
      );
    DafnySequence<? extends Character> message =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.getMessage()
      );
    return Error.create_CollectionOfErrors(list, message);
  }

  public static GetConstraintsInput GetConstraintsInput(
    simple.constraints.model.GetConstraintsInput nativeValue
  ) {
    Option<DafnySequence<? extends Character>> myString;
    myString =
      Objects.nonNull(nativeValue.MyString())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.MyString()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> nonEmptyString;
    nonEmptyString =
      Objects.nonNull(nativeValue.NonEmptyString())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.NonEmptyString()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> stringLessThanOrEqualToTen;
    stringLessThanOrEqualToTen =
      Objects.nonNull(nativeValue.StringLessThanOrEqualToTen())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.StringLessThanOrEqualToTen()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Byte>> myBlob;
    myBlob =
      Objects.nonNull(nativeValue.MyBlob())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
            nativeValue.MyBlob()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
        );
    Option<DafnySequence<? extends Byte>> nonEmptyBlob;
    nonEmptyBlob =
      Objects.nonNull(nativeValue.NonEmptyBlob())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
            nativeValue.NonEmptyBlob()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
        );
    Option<DafnySequence<? extends Byte>> blobLessThanOrEqualToTen;
    blobLessThanOrEqualToTen =
      Objects.nonNull(nativeValue.BlobLessThanOrEqualToTen())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
            nativeValue.BlobLessThanOrEqualToTen()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
        );
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> myList;
    myList =
      (Objects.nonNull(nativeValue.MyList()) && nativeValue.MyList().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.MyList(nativeValue.MyList())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnySequence<? extends DafnySequence<? extends Character>>
    > nonEmptyList;
    nonEmptyList =
      (Objects.nonNull(nativeValue.NonEmptyList()) &&
          nativeValue.NonEmptyList().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.NonEmptyList(nativeValue.NonEmptyList())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnySequence<? extends DafnySequence<? extends Character>>
    > listLessThanOrEqualToTen;
    listLessThanOrEqualToTen =
      (Objects.nonNull(nativeValue.ListLessThanOrEqualToTen()) &&
          nativeValue.ListLessThanOrEqualToTen().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.ListLessThanOrEqualToTen(
            nativeValue.ListLessThanOrEqualToTen()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Character>,
        ? extends DafnySequence<? extends Character>
      >
    > myMap;
    myMap =
      (Objects.nonNull(nativeValue.MyMap()) && nativeValue.MyMap().size() > 0)
        ? Option.create_Some(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.MyMap(nativeValue.MyMap())
        )
        : Option.create_None(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Character>,
        ? extends DafnySequence<? extends Character>
      >
    > nonEmptyMap;
    nonEmptyMap =
      (Objects.nonNull(nativeValue.NonEmptyMap()) &&
          nativeValue.NonEmptyMap().size() > 0)
        ? Option.create_Some(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.NonEmptyMap(nativeValue.NonEmptyMap())
        )
        : Option.create_None(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Character>,
        ? extends DafnySequence<? extends Character>
      >
    > mapLessThanOrEqualToTen;
    mapLessThanOrEqualToTen =
      (Objects.nonNull(nativeValue.MapLessThanOrEqualToTen()) &&
          nativeValue.MapLessThanOrEqualToTen().size() > 0)
        ? Option.create_Some(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.MapLessThanOrEqualToTen(nativeValue.MapLessThanOrEqualToTen())
        )
        : Option.create_None(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<Integer> oneToTen;
    oneToTen =
      Objects.nonNull(nativeValue.OneToTen())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.OneToTen()))
        : Option.create_None(TypeDescriptor.INT);
    Option<Long> myTenToTen;
    myTenToTen =
      Objects.nonNull(nativeValue.myTenToTen())
        ? Option.create_Some(TypeDescriptor.LONG, (nativeValue.myTenToTen()))
        : Option.create_None(TypeDescriptor.LONG);
    Option<Integer> greaterThanOne;
    greaterThanOne =
      Objects.nonNull(nativeValue.GreaterThanOne())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.GreaterThanOne()))
        : Option.create_None(TypeDescriptor.INT);
    Option<Integer> lessThanTen;
    lessThanTen =
      Objects.nonNull(nativeValue.LessThanTen())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.LessThanTen()))
        : Option.create_None(TypeDescriptor.INT);
    Option<DafnySequence<? extends Byte>> myUtf8Bytes;
    myUtf8Bytes =
      Objects.nonNull(nativeValue.MyUtf8Bytes())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(
            nativeValue.MyUtf8Bytes()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
        );
    Option<
      DafnySequence<? extends DafnySequence<? extends Byte>>
    > myListOfUtf8Bytes;
    myListOfUtf8Bytes =
      (Objects.nonNull(nativeValue.MyListOfUtf8Bytes()) &&
          nativeValue.MyListOfUtf8Bytes().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
          ),
          ToDafny.ListOfUtf8Bytes(nativeValue.MyListOfUtf8Bytes())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
          )
        );
    return new GetConstraintsInput(
      myString,
      nonEmptyString,
      stringLessThanOrEqualToTen,
      myBlob,
      nonEmptyBlob,
      blobLessThanOrEqualToTen,
      myList,
      nonEmptyList,
      listLessThanOrEqualToTen,
      myMap,
      nonEmptyMap,
      mapLessThanOrEqualToTen,
      oneToTen,
      myTenToTen,
      greaterThanOne,
      lessThanTen,
      myUtf8Bytes,
      myListOfUtf8Bytes
    );
  }

  public static GetConstraintsOutput GetConstraintsOutput(
    simple.constraints.model.GetConstraintsOutput nativeValue
  ) {
    Option<DafnySequence<? extends Character>> myString;
    myString =
      Objects.nonNull(nativeValue.MyString())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.MyString()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> nonEmptyString;
    nonEmptyString =
      Objects.nonNull(nativeValue.NonEmptyString())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.NonEmptyString()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Character>> stringLessThanOrEqualToTen;
    stringLessThanOrEqualToTen =
      Objects.nonNull(nativeValue.StringLessThanOrEqualToTen())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
            nativeValue.StringLessThanOrEqualToTen()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
        );
    Option<DafnySequence<? extends Byte>> myBlob;
    myBlob =
      Objects.nonNull(nativeValue.MyBlob())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
            nativeValue.MyBlob()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
        );
    Option<DafnySequence<? extends Byte>> nonEmptyBlob;
    nonEmptyBlob =
      Objects.nonNull(nativeValue.NonEmptyBlob())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
            nativeValue.NonEmptyBlob()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
        );
    Option<DafnySequence<? extends Byte>> blobLessThanOrEqualToTen;
    blobLessThanOrEqualToTen =
      Objects.nonNull(nativeValue.BlobLessThanOrEqualToTen())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.ByteSequence(
            nativeValue.BlobLessThanOrEqualToTen()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
        );
    Option<DafnySequence<? extends DafnySequence<? extends Character>>> myList;
    myList =
      (Objects.nonNull(nativeValue.MyList()) && nativeValue.MyList().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.MyList(nativeValue.MyList())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnySequence<? extends DafnySequence<? extends Character>>
    > nonEmptyList;
    nonEmptyList =
      (Objects.nonNull(nativeValue.NonEmptyList()) &&
          nativeValue.NonEmptyList().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.NonEmptyList(nativeValue.NonEmptyList())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnySequence<? extends DafnySequence<? extends Character>>
    > listLessThanOrEqualToTen;
    listLessThanOrEqualToTen =
      (Objects.nonNull(nativeValue.ListLessThanOrEqualToTen()) &&
          nativeValue.ListLessThanOrEqualToTen().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.ListLessThanOrEqualToTen(
            nativeValue.ListLessThanOrEqualToTen()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Character>,
        ? extends DafnySequence<? extends Character>
      >
    > myMap;
    myMap =
      (Objects.nonNull(nativeValue.MyMap()) && nativeValue.MyMap().size() > 0)
        ? Option.create_Some(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.MyMap(nativeValue.MyMap())
        )
        : Option.create_None(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Character>,
        ? extends DafnySequence<? extends Character>
      >
    > nonEmptyMap;
    nonEmptyMap =
      (Objects.nonNull(nativeValue.NonEmptyMap()) &&
          nativeValue.NonEmptyMap().size() > 0)
        ? Option.create_Some(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.NonEmptyMap(nativeValue.NonEmptyMap())
        )
        : Option.create_None(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<
      DafnyMap<
        ? extends DafnySequence<? extends Character>,
        ? extends DafnySequence<? extends Character>
      >
    > mapLessThanOrEqualToTen;
    mapLessThanOrEqualToTen =
      (Objects.nonNull(nativeValue.MapLessThanOrEqualToTen()) &&
          nativeValue.MapLessThanOrEqualToTen().size() > 0)
        ? Option.create_Some(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          ),
          ToDafny.MapLessThanOrEqualToTen(nativeValue.MapLessThanOrEqualToTen())
        )
        : Option.create_None(
          DafnyMap._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
            DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
          )
        );
    Option<Integer> oneToTen;
    oneToTen =
      Objects.nonNull(nativeValue.OneToTen())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.OneToTen()))
        : Option.create_None(TypeDescriptor.INT);
    Option<Long> thatTenToTen;
    thatTenToTen =
      Objects.nonNull(nativeValue.thatTenToTen())
        ? Option.create_Some(TypeDescriptor.LONG, (nativeValue.thatTenToTen()))
        : Option.create_None(TypeDescriptor.LONG);
    Option<Integer> greaterThanOne;
    greaterThanOne =
      Objects.nonNull(nativeValue.GreaterThanOne())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.GreaterThanOne()))
        : Option.create_None(TypeDescriptor.INT);
    Option<Integer> lessThanTen;
    lessThanTen =
      Objects.nonNull(nativeValue.LessThanTen())
        ? Option.create_Some(TypeDescriptor.INT, (nativeValue.LessThanTen()))
        : Option.create_None(TypeDescriptor.INT);
    Option<DafnySequence<? extends Byte>> myUtf8Bytes;
    myUtf8Bytes =
      Objects.nonNull(nativeValue.MyUtf8Bytes())
        ? Option.create_Some(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE),
          software.amazon.smithy.dafny.conversion.ToDafny.Simple.DafnyUtf8Bytes(
            nativeValue.MyUtf8Bytes()
          )
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
        );
    Option<
      DafnySequence<? extends DafnySequence<? extends Byte>>
    > myListOfUtf8Bytes;
    myListOfUtf8Bytes =
      (Objects.nonNull(nativeValue.MyListOfUtf8Bytes()) &&
          nativeValue.MyListOfUtf8Bytes().size() > 0)
        ? Option.create_Some(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
          ),
          ToDafny.ListOfUtf8Bytes(nativeValue.MyListOfUtf8Bytes())
        )
        : Option.create_None(
          DafnySequence._typeDescriptor(
            DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
          )
        );
    return new GetConstraintsOutput(
      myString,
      nonEmptyString,
      stringLessThanOrEqualToTen,
      myBlob,
      nonEmptyBlob,
      blobLessThanOrEqualToTen,
      myList,
      nonEmptyList,
      listLessThanOrEqualToTen,
      myMap,
      nonEmptyMap,
      mapLessThanOrEqualToTen,
      oneToTen,
      thatTenToTen,
      greaterThanOne,
      lessThanTen,
      myUtf8Bytes,
      myListOfUtf8Bytes
    );
  }

  public static SimpleConstraintsConfig SimpleConstraintsConfig(
    simple.constraints.model.SimpleConstraintsConfig nativeValue
  ) {
    return new SimpleConstraintsConfig();
  }

  public static Error Error(SimpleConstraintsException nativeValue) {
    DafnySequence<? extends Character> message;
    message =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        nativeValue.message()
      );
    return new Error_SimpleConstraintsException(message);
  }

  public static DafnySequence<
    ? extends DafnySequence<? extends Character>
  > ListLessThanOrEqualToTen(List<String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
      DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
    );
  }

  public static DafnySequence<
    ? extends DafnySequence<? extends Byte>
  > ListOfUtf8Bytes(List<String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::DafnyUtf8Bytes,
      DafnySequence._typeDescriptor(TypeDescriptor.BYTE)
    );
  }

  public static DafnySequence<
    ? extends DafnySequence<? extends Character>
  > MyList(List<String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
      DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
    );
  }

  public static DafnySequence<
    ? extends DafnySequence<? extends Character>
  > NonEmptyList(List<String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
      DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
    );
  }

  public static DafnyMap<
    ? extends DafnySequence<? extends Character>,
    ? extends DafnySequence<? extends Character>
  > MapLessThanOrEqualToTen(Map<String, String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToMap(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence
    );
  }

  public static DafnyMap<
    ? extends DafnySequence<? extends Character>,
    ? extends DafnySequence<? extends Character>
  > MyMap(Map<String, String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToMap(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence
    );
  }

  public static DafnyMap<
    ? extends DafnySequence<? extends Character>,
    ? extends DafnySequence<? extends Character>
  > NonEmptyMap(Map<String, String> nativeValue) {
    return software.amazon.smithy.dafny.conversion.ToDafny.Aggregate.GenericToMap(
      nativeValue,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence,
      software.amazon.smithy.dafny.conversion.ToDafny.Simple::CharacterSequence
    );
  }

  public static ISimpleConstraintsClient SimpleConstraints(
    SimpleConstraints nativeValue
  ) {
    return nativeValue.impl();
  }
}
