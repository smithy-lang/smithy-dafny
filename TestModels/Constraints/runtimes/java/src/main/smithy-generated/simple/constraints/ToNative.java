// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.constraints;

import dafny.DafnyMap;
import dafny.DafnySequence;
import java.lang.Byte;
import java.lang.Character;
import java.lang.RuntimeException;
import java.lang.String;
import java.util.List;
import java.util.Map;
import simple.constraints.internaldafny.types.Error;
import simple.constraints.internaldafny.types.Error_CollectionOfErrors;
import simple.constraints.internaldafny.types.Error_Opaque;
import simple.constraints.internaldafny.types.Error_SimpleConstraintsException;
import simple.constraints.internaldafny.types.ISimpleConstraintsClient;
import simple.constraints.model.CollectionOfErrors;
import simple.constraints.model.GetConstraintsInput;
import simple.constraints.model.GetConstraintsOutput;
import simple.constraints.model.OpaqueError;
import simple.constraints.model.SimpleConstraintsConfig;
import simple.constraints.model.SimpleConstraintsException;

public class ToNative {

  public static OpaqueError Error(Error_Opaque dafnyValue) {
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue.dtor_obj());
    return nativeBuilder.build();
  }

  public static CollectionOfErrors Error(Error_CollectionOfErrors dafnyValue) {
    CollectionOfErrors.Builder nativeBuilder = CollectionOfErrors.builder();
    nativeBuilder.list(
      software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue.dtor_list(),
        ToNative::Error
      )
    );
    nativeBuilder.message(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_message()
      )
    );
    return nativeBuilder.build();
  }

  public static SimpleConstraintsException Error(
    Error_SimpleConstraintsException dafnyValue
  ) {
    SimpleConstraintsException.Builder nativeBuilder =
      SimpleConstraintsException.builder();
    nativeBuilder.message(
      software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
        dafnyValue.dtor_message()
      )
    );
    return nativeBuilder.build();
  }

  public static RuntimeException Error(Error dafnyValue) {
    if (dafnyValue.is_SimpleConstraintsException()) {
      return ToNative.Error((Error_SimpleConstraintsException) dafnyValue);
    }
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    if (dafnyValue.is_CollectionOfErrors()) {
      return ToNative.Error((Error_CollectionOfErrors) dafnyValue);
    }
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue);
    return nativeBuilder.build();
  }

  public static GetConstraintsInput GetConstraintsInput(
    simple.constraints.internaldafny.types.GetConstraintsInput dafnyValue
  ) {
    GetConstraintsInput.Builder nativeBuilder = GetConstraintsInput.builder();
    if (dafnyValue.dtor_MyString().is_Some()) {
      nativeBuilder.MyString(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_MyString().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_NonEmptyString().is_Some()) {
      nativeBuilder.NonEmptyString(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_NonEmptyString().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_StringLessThanOrEqualToTen().is_Some()) {
      nativeBuilder.StringLessThanOrEqualToTen(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_StringLessThanOrEqualToTen().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_MyBlob().is_Some()) {
      nativeBuilder.MyBlob(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(
          dafnyValue.dtor_MyBlob().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_NonEmptyBlob().is_Some()) {
      nativeBuilder.NonEmptyBlob(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(
          dafnyValue.dtor_NonEmptyBlob().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_BlobLessThanOrEqualToTen().is_Some()) {
      nativeBuilder.BlobLessThanOrEqualToTen(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(
          dafnyValue.dtor_BlobLessThanOrEqualToTen().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_MyList().is_Some()) {
      nativeBuilder.MyList(
        ToNative.MyList(dafnyValue.dtor_MyList().dtor_value())
      );
    }
    if (dafnyValue.dtor_NonEmptyList().is_Some()) {
      nativeBuilder.NonEmptyList(
        ToNative.NonEmptyList(dafnyValue.dtor_NonEmptyList().dtor_value())
      );
    }
    if (dafnyValue.dtor_ListLessThanOrEqualToTen().is_Some()) {
      nativeBuilder.ListLessThanOrEqualToTen(
        ToNative.ListLessThanOrEqualToTen(
          dafnyValue.dtor_ListLessThanOrEqualToTen().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_MyMap().is_Some()) {
      nativeBuilder.MyMap(ToNative.MyMap(dafnyValue.dtor_MyMap().dtor_value()));
    }
    if (dafnyValue.dtor_NonEmptyMap().is_Some()) {
      nativeBuilder.NonEmptyMap(
        ToNative.NonEmptyMap(dafnyValue.dtor_NonEmptyMap().dtor_value())
      );
    }
    if (dafnyValue.dtor_MapLessThanOrEqualToTen().is_Some()) {
      nativeBuilder.MapLessThanOrEqualToTen(
        ToNative.MapLessThanOrEqualToTen(
          dafnyValue.dtor_MapLessThanOrEqualToTen().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_OneToTen().is_Some()) {
      nativeBuilder.OneToTen((dafnyValue.dtor_OneToTen().dtor_value()));
    }
    if (dafnyValue.dtor_myTenToTen().is_Some()) {
      nativeBuilder.myTenToTen((dafnyValue.dtor_myTenToTen().dtor_value()));
    }
    if (dafnyValue.dtor_GreaterThanOne().is_Some()) {
      nativeBuilder.GreaterThanOne(
        (dafnyValue.dtor_GreaterThanOne().dtor_value())
      );
    }
    if (dafnyValue.dtor_LessThanTen().is_Some()) {
      nativeBuilder.LessThanTen((dafnyValue.dtor_LessThanTen().dtor_value()));
    }
    if (dafnyValue.dtor_MyUtf8Bytes().is_Some()) {
      nativeBuilder.MyUtf8Bytes(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(
          dafnyValue.dtor_MyUtf8Bytes().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_MyListOfUtf8Bytes().is_Some()) {
      nativeBuilder.MyListOfUtf8Bytes(
        ToNative.ListOfUtf8Bytes(
          dafnyValue.dtor_MyListOfUtf8Bytes().dtor_value()
        )
      );
    }
    return nativeBuilder.build();
  }

  public static GetConstraintsOutput GetConstraintsOutput(
    simple.constraints.internaldafny.types.GetConstraintsOutput dafnyValue
  ) {
    GetConstraintsOutput.Builder nativeBuilder = GetConstraintsOutput.builder();
    if (dafnyValue.dtor_MyString().is_Some()) {
      nativeBuilder.MyString(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_MyString().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_NonEmptyString().is_Some()) {
      nativeBuilder.NonEmptyString(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_NonEmptyString().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_StringLessThanOrEqualToTen().is_Some()) {
      nativeBuilder.StringLessThanOrEqualToTen(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.String(
          dafnyValue.dtor_StringLessThanOrEqualToTen().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_MyBlob().is_Some()) {
      nativeBuilder.MyBlob(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(
          dafnyValue.dtor_MyBlob().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_NonEmptyBlob().is_Some()) {
      nativeBuilder.NonEmptyBlob(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(
          dafnyValue.dtor_NonEmptyBlob().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_BlobLessThanOrEqualToTen().is_Some()) {
      nativeBuilder.BlobLessThanOrEqualToTen(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.ByteBuffer(
          dafnyValue.dtor_BlobLessThanOrEqualToTen().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_MyList().is_Some()) {
      nativeBuilder.MyList(
        ToNative.MyList(dafnyValue.dtor_MyList().dtor_value())
      );
    }
    if (dafnyValue.dtor_NonEmptyList().is_Some()) {
      nativeBuilder.NonEmptyList(
        ToNative.NonEmptyList(dafnyValue.dtor_NonEmptyList().dtor_value())
      );
    }
    if (dafnyValue.dtor_ListLessThanOrEqualToTen().is_Some()) {
      nativeBuilder.ListLessThanOrEqualToTen(
        ToNative.ListLessThanOrEqualToTen(
          dafnyValue.dtor_ListLessThanOrEqualToTen().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_MyMap().is_Some()) {
      nativeBuilder.MyMap(ToNative.MyMap(dafnyValue.dtor_MyMap().dtor_value()));
    }
    if (dafnyValue.dtor_NonEmptyMap().is_Some()) {
      nativeBuilder.NonEmptyMap(
        ToNative.NonEmptyMap(dafnyValue.dtor_NonEmptyMap().dtor_value())
      );
    }
    if (dafnyValue.dtor_MapLessThanOrEqualToTen().is_Some()) {
      nativeBuilder.MapLessThanOrEqualToTen(
        ToNative.MapLessThanOrEqualToTen(
          dafnyValue.dtor_MapLessThanOrEqualToTen().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_OneToTen().is_Some()) {
      nativeBuilder.OneToTen((dafnyValue.dtor_OneToTen().dtor_value()));
    }
    if (dafnyValue.dtor_thatTenToTen().is_Some()) {
      nativeBuilder.thatTenToTen((dafnyValue.dtor_thatTenToTen().dtor_value()));
    }
    if (dafnyValue.dtor_GreaterThanOne().is_Some()) {
      nativeBuilder.GreaterThanOne(
        (dafnyValue.dtor_GreaterThanOne().dtor_value())
      );
    }
    if (dafnyValue.dtor_LessThanTen().is_Some()) {
      nativeBuilder.LessThanTen((dafnyValue.dtor_LessThanTen().dtor_value()));
    }
    if (dafnyValue.dtor_MyUtf8Bytes().is_Some()) {
      nativeBuilder.MyUtf8Bytes(
        software.amazon.smithy.dafny.conversion.ToNative.Simple.DafnyUtf8Bytes(
          dafnyValue.dtor_MyUtf8Bytes().dtor_value()
        )
      );
    }
    if (dafnyValue.dtor_MyListOfUtf8Bytes().is_Some()) {
      nativeBuilder.MyListOfUtf8Bytes(
        ToNative.ListOfUtf8Bytes(
          dafnyValue.dtor_MyListOfUtf8Bytes().dtor_value()
        )
      );
    }
    return nativeBuilder.build();
  }

  public static SimpleConstraintsConfig SimpleConstraintsConfig(
    simple.constraints.internaldafny.types.SimpleConstraintsConfig dafnyValue
  ) {
    SimpleConstraintsConfig.Builder nativeBuilder =
      SimpleConstraintsConfig.builder();
    return nativeBuilder.build();
  }

  public static List<String> ListLessThanOrEqualToTen(
    DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
      dafnyValue,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String
    );
  }

  public static List<String> ListOfUtf8Bytes(
    DafnySequence<? extends DafnySequence<? extends Byte>> dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
      dafnyValue,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::DafnyUtf8Bytes
    );
  }

  public static List<String> MyList(
    DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
      dafnyValue,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String
    );
  }

  public static List<String> NonEmptyList(
    DafnySequence<? extends DafnySequence<? extends Character>> dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToList(
      dafnyValue,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String
    );
  }

  public static Map<String, String> MapLessThanOrEqualToTen(
    DafnyMap<
      ? extends DafnySequence<? extends Character>,
      ? extends DafnySequence<? extends Character>
    > dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
      dafnyValue,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String
    );
  }

  public static Map<String, String> MyMap(
    DafnyMap<
      ? extends DafnySequence<? extends Character>,
      ? extends DafnySequence<? extends Character>
    > dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
      dafnyValue,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String
    );
  }

  public static Map<String, String> NonEmptyMap(
    DafnyMap<
      ? extends DafnySequence<? extends Character>,
      ? extends DafnySequence<? extends Character>
    > dafnyValue
  ) {
    return software.amazon.smithy.dafny.conversion.ToNative.Aggregate.GenericToMap(
      dafnyValue,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String,
      software.amazon.smithy.dafny.conversion.ToNative.Simple::String
    );
  }

  public static SimpleConstraints SimpleConstraints(
    ISimpleConstraintsClient dafnyValue
  ) {
    return new SimpleConstraints(dafnyValue);
  }
}
