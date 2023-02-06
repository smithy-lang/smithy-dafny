// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System.Linq;
using System;
namespace Simple.Resources.Wrapped
{
    public static class TypeConversion
    {
        internal static Simple.Resources.GetResourceDataInput FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput(Dafny.Simple.Resources.Types._IGetResourceDataInput value)
        {
            Dafny.Simple.Resources.Types.GetResourceDataInput concrete = (Dafny.Simple.Resources.Types.GetResourceDataInput)value; Simple.Resources.GetResourceDataInput converted = new Simple.Resources.GetResourceDataInput(); if (concrete._blobValue.is_Some) converted.BlobValue = (System.IO.MemoryStream)FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M9_blobValue(concrete._blobValue);
            if (concrete._booleanValue.is_Some) converted.BooleanValue = (bool)FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M12_booleanValue(concrete._booleanValue);
            if (concrete._stringValue.is_Some) converted.StringValue = (string)FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M11_stringValue(concrete._stringValue);
            if (concrete._integerValue.is_Some) converted.IntegerValue = (int)FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M12_integerValue(concrete._integerValue);
            if (concrete._longValue.is_Some) converted.LongValue = (long)FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M9_longValue(concrete._longValue); return converted;
        }
        internal static Dafny.Simple.Resources.Types._IGetResourceDataInput ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput(Simple.Resources.GetResourceDataInput value)
        {
            System.IO.MemoryStream var_blobValue = value.IsSetBlobValue() ? value.BlobValue : (System.IO.MemoryStream)null;
            bool? var_booleanValue = value.IsSetBooleanValue() ? value.BooleanValue : (bool?)null;
            string var_stringValue = value.IsSetStringValue() ? value.StringValue : (string)null;
            int? var_integerValue = value.IsSetIntegerValue() ? value.IntegerValue : (int?)null;
            long? var_longValue = value.IsSetLongValue() ? value.LongValue : (long?)null;
            return new Dafny.Simple.Resources.Types.GetResourceDataInput(ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M9_blobValue(var_blobValue), ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M12_booleanValue(var_booleanValue), ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M11_stringValue(var_stringValue), ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M12_integerValue(var_integerValue), ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M9_longValue(var_longValue));
        }
        internal static Simple.Resources.GetResourceDataOutput FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput(Dafny.Simple.Resources.Types._IGetResourceDataOutput value)
        {
            Dafny.Simple.Resources.Types.GetResourceDataOutput concrete = (Dafny.Simple.Resources.Types.GetResourceDataOutput)value; Simple.Resources.GetResourceDataOutput converted = new Simple.Resources.GetResourceDataOutput(); if (concrete._blobValue.is_Some) converted.BlobValue = (System.IO.MemoryStream)FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M9_blobValue(concrete._blobValue);
            if (concrete._booleanValue.is_Some) converted.BooleanValue = (bool)FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M12_booleanValue(concrete._booleanValue);
            if (concrete._stringValue.is_Some) converted.StringValue = (string)FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M11_stringValue(concrete._stringValue);
            if (concrete._integerValue.is_Some) converted.IntegerValue = (int)FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M12_integerValue(concrete._integerValue);
            if (concrete._longValue.is_Some) converted.LongValue = (long)FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M9_longValue(concrete._longValue); return converted;
        }
        internal static Dafny.Simple.Resources.Types._IGetResourceDataOutput ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput(Simple.Resources.GetResourceDataOutput value)
        {
            System.IO.MemoryStream var_blobValue = value.IsSetBlobValue() ? value.BlobValue : (System.IO.MemoryStream)null;
            bool? var_booleanValue = value.IsSetBooleanValue() ? value.BooleanValue : (bool?)null;
            string var_stringValue = value.IsSetStringValue() ? value.StringValue : (string)null;
            int? var_integerValue = value.IsSetIntegerValue() ? value.IntegerValue : (int?)null;
            long? var_longValue = value.IsSetLongValue() ? value.LongValue : (long?)null;
            return new Dafny.Simple.Resources.Types.GetResourceDataOutput(ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M9_blobValue(var_blobValue), ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M12_booleanValue(var_booleanValue), ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M11_stringValue(var_stringValue), ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M12_integerValue(var_integerValue), ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M9_longValue(var_longValue));
        }
        internal static Simple.Resources.GetResourcesInput FromDafny_N6_simple__N9_resources__S17_GetResourcesInput(Dafny.Simple.Resources.Types._IGetResourcesInput value)
        {
            Dafny.Simple.Resources.Types.GetResourcesInput concrete = (Dafny.Simple.Resources.Types.GetResourcesInput)value; Simple.Resources.GetResourcesInput converted = new Simple.Resources.GetResourcesInput(); if (concrete._value.is_Some) converted.Value = (string)FromDafny_N6_simple__N9_resources__S17_GetResourcesInput__M5_value(concrete._value); return converted;
        }
        internal static Dafny.Simple.Resources.Types._IGetResourcesInput ToDafny_N6_simple__N9_resources__S17_GetResourcesInput(Simple.Resources.GetResourcesInput value)
        {
            string var_value = value.IsSetValue() ? value.Value : (string)null;
            return new Dafny.Simple.Resources.Types.GetResourcesInput(ToDafny_N6_simple__N9_resources__S17_GetResourcesInput__M5_value(var_value));
        }
        internal static Simple.Resources.GetResourcesOutput FromDafny_N6_simple__N9_resources__S18_GetResourcesOutput(Dafny.Simple.Resources.Types._IGetResourcesOutput value)
        {
            Dafny.Simple.Resources.Types.GetResourcesOutput concrete = (Dafny.Simple.Resources.Types.GetResourcesOutput)value; Simple.Resources.GetResourcesOutput converted = new Simple.Resources.GetResourcesOutput(); converted.Output = (Simple.Resources.ISimpleResource)FromDafny_N6_simple__N9_resources__S18_GetResourcesOutput__M6_output(concrete._output); return converted;
        }
        internal static Dafny.Simple.Resources.Types._IGetResourcesOutput ToDafny_N6_simple__N9_resources__S18_GetResourcesOutput(Simple.Resources.GetResourcesOutput value)
        {

            return new Dafny.Simple.Resources.Types.GetResourcesOutput(ToDafny_N6_simple__N9_resources__S18_GetResourcesOutput__M6_output(value.Output));
        }
        internal static Simple.Resources.SimpleResourcesConfig FromDafny_N6_simple__N9_resources__S21_SimpleResourcesConfig(Dafny.Simple.Resources.Types._ISimpleResourcesConfig value)
        {
            Dafny.Simple.Resources.Types.SimpleResourcesConfig concrete = (Dafny.Simple.Resources.Types.SimpleResourcesConfig)value; Simple.Resources.SimpleResourcesConfig converted = new Simple.Resources.SimpleResourcesConfig(); converted.Name = (string)FromDafny_N6_simple__N9_resources__S21_SimpleResourcesConfig__M4_name(concrete._name); return converted;
        }
        internal static Dafny.Simple.Resources.Types._ISimpleResourcesConfig ToDafny_N6_simple__N9_resources__S21_SimpleResourcesConfig(Simple.Resources.SimpleResourcesConfig value)
        {

            return new Dafny.Simple.Resources.Types.SimpleResourcesConfig(ToDafny_N6_simple__N9_resources__S21_SimpleResourcesConfig__M4_name(value.Name));
        }
        internal static Simple.Resources.SimpleResourcesException FromDafny_N6_simple__N9_resources__S24_SimpleResourcesException(Dafny.Simple.Resources.Types.Error_SimpleResourcesException value)
        {
            return new Simple.Resources.SimpleResourcesException(
            FromDafny_N6_simple__N9_resources__S24_SimpleResourcesException__M7_message(value._message)
            );
        }
        internal static Dafny.Simple.Resources.Types.Error_SimpleResourcesException ToDafny_N6_simple__N9_resources__S24_SimpleResourcesException(Simple.Resources.SimpleResourcesException value)
        {

            return new Dafny.Simple.Resources.Types.Error_SimpleResourcesException(
            ToDafny_N6_simple__N9_resources__S24_SimpleResourcesException__M7_message(value.Message)
            );
        }
        internal static System.IO.MemoryStream FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M9_blobValue(Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }
        internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M9_blobValue(System.IO.MemoryStream value)
        {
            return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }
        internal static bool? FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M12_booleanValue(Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None ? (bool?)null : FromDafny_N6_smithy__N3_api__S7_Boolean(value.Extract());
        }
        internal static Wrappers_Compile._IOption<bool> ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M12_booleanValue(bool? value)
        {
            return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N6_smithy__N3_api__S7_Boolean((bool)value));
        }
        internal static string FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M11_stringValue(Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None ? (string)null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
        }
        internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M11_stringValue(string value)
        {
            return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string)value));
        }
        internal static int? FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M12_integerValue(Wrappers_Compile._IOption<int> value)
        {
            return value.is_None ? (int?)null : FromDafny_N6_smithy__N3_api__S7_Integer(value.Extract());
        }
        internal static Wrappers_Compile._IOption<int> ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M12_integerValue(int? value)
        {
            return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N6_smithy__N3_api__S7_Integer((int)value));
        }
        internal static long? FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M9_longValue(Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }
        internal static Wrappers_Compile._IOption<long> ToDafny_N6_simple__N9_resources__S20_GetResourceDataInput__M9_longValue(long? value)
        {
            return value == null ? Wrappers_Compile.Option<long>.create_None() : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
        }
        internal static System.IO.MemoryStream FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M9_blobValue(Wrappers_Compile._IOption<Dafny.ISequence<byte>> value)
        {
            return value.is_None ? (System.IO.MemoryStream)null : FromDafny_N6_smithy__N3_api__S4_Blob(value.Extract());
        }
        internal static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M9_blobValue(System.IO.MemoryStream value)
        {
            return value == null ? Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(ToDafny_N6_smithy__N3_api__S4_Blob((System.IO.MemoryStream)value));
        }
        internal static bool? FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M12_booleanValue(Wrappers_Compile._IOption<bool> value)
        {
            return value.is_None ? (bool?)null : FromDafny_N6_smithy__N3_api__S7_Boolean(value.Extract());
        }
        internal static Wrappers_Compile._IOption<bool> ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M12_booleanValue(bool? value)
        {
            return value == null ? Wrappers_Compile.Option<bool>.create_None() : Wrappers_Compile.Option<bool>.create_Some(ToDafny_N6_smithy__N3_api__S7_Boolean((bool)value));
        }
        internal static string FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M11_stringValue(Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None ? (string)null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
        }
        internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M11_stringValue(string value)
        {
            return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string)value));
        }
        internal static int? FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M12_integerValue(Wrappers_Compile._IOption<int> value)
        {
            return value.is_None ? (int?)null : FromDafny_N6_smithy__N3_api__S7_Integer(value.Extract());
        }
        internal static Wrappers_Compile._IOption<int> ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M12_integerValue(int? value)
        {
            return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N6_smithy__N3_api__S7_Integer((int)value));
        }
        internal static long? FromDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M9_longValue(Wrappers_Compile._IOption<long> value)
        {
            return value.is_None ? (long?)null : FromDafny_N6_smithy__N3_api__S4_Long(value.Extract());
        }
        internal static Wrappers_Compile._IOption<long> ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput__M9_longValue(long? value)
        {
            return value == null ? Wrappers_Compile.Option<long>.create_None() : Wrappers_Compile.Option<long>.create_Some(ToDafny_N6_smithy__N3_api__S4_Long((long)value));
        }
        internal static string FromDafny_N6_simple__N9_resources__S17_GetResourcesInput__M5_value(Wrappers_Compile._IOption<Dafny.ISequence<char>> value)
        {
            return value.is_None ? (string)null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
        }
        internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N6_simple__N9_resources__S17_GetResourcesInput__M5_value(string value)
        {
            return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string)value));
        }
        internal static Simple.Resources.ISimpleResource FromDafny_N6_simple__N9_resources__S18_GetResourcesOutput__M6_output(Dafny.Simple.Resources.Types.ISimpleResource value)
        {
            return FromDafny_N6_simple__N9_resources__S23_SimpleResourceReference(value);
        }
        internal static Dafny.Simple.Resources.Types.ISimpleResource ToDafny_N6_simple__N9_resources__S18_GetResourcesOutput__M6_output(Simple.Resources.ISimpleResource value)
        {
            return ToDafny_N6_simple__N9_resources__S23_SimpleResourceReference(value);
        }
        internal static string FromDafny_N6_simple__N9_resources__S21_SimpleResourcesConfig__M4_name(Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }
        internal static Dafny.ISequence<char> ToDafny_N6_simple__N9_resources__S21_SimpleResourcesConfig__M4_name(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }
        internal static string FromDafny_N6_simple__N9_resources__S24_SimpleResourcesException__M7_message(Dafny.ISequence<char> value)
        {
            return FromDafny_N6_smithy__N3_api__S6_String(value);
        }
        internal static Dafny.ISequence<char> ToDafny_N6_simple__N9_resources__S24_SimpleResourcesException__M7_message(string value)
        {
            return ToDafny_N6_smithy__N3_api__S6_String(value);
        }
        internal static System.IO.MemoryStream FromDafny_N6_smithy__N3_api__S4_Blob(Dafny.ISequence<byte> value)
        {
            return new System.IO.MemoryStream(value.Elements);
        }
        internal static Dafny.ISequence<byte> ToDafny_N6_smithy__N3_api__S4_Blob(System.IO.MemoryStream value)
        {
            return Dafny.Sequence<byte>.FromArray(value.ToArray());
        }
        internal static bool FromDafny_N6_smithy__N3_api__S7_Boolean(bool value)
        {
            return value;
        }
        internal static bool ToDafny_N6_smithy__N3_api__S7_Boolean(bool value)
        {
            return value;
        }
        internal static string FromDafny_N6_smithy__N3_api__S6_String(Dafny.ISequence<char> value)
        {
            return new string(value.Elements);
        }
        internal static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String(string value)
        {
            return Dafny.Sequence<char>.FromString(value);
        }
        internal static int FromDafny_N6_smithy__N3_api__S7_Integer(int value)
        {
            return value;
        }
        internal static int ToDafny_N6_smithy__N3_api__S7_Integer(int value)
        {
            return value;
        }
        internal static long FromDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }
        internal static long ToDafny_N6_smithy__N3_api__S4_Long(long value)
        {
            return value;
        }
        internal static Simple.Resources.ISimpleResource FromDafny_N6_simple__N9_resources__S23_SimpleResourceReference(Dafny.Simple.Resources.Types.ISimpleResource value)
        {
            // This is converting a reference type in a dependant module.
            // Therefore it defers to the dependant module for conversion
            return Simple.Resources.TypeConversion.FromDafny_N6_simple__N9_resources__S23_SimpleResourceReference(value);
        }
        internal static Dafny.Simple.Resources.Types.ISimpleResource ToDafny_N6_simple__N9_resources__S23_SimpleResourceReference(Simple.Resources.ISimpleResource value)
        {
            // This is converting a reference type in a dependant module.
            // Therefore it defers to the dependant module for conversion
            return Simple.Resources.TypeConversion.ToDafny_N6_simple__N9_resources__S23_SimpleResourceReference(value);
        }
        public static System.Exception FromDafny_CommonError(Dafny.Simple.Resources.Types._IError value)
        {
            switch (value)
            {
                case Dafny.Simple.Resources.Types.Error_SimpleResourcesException dafnyVal:
                    return FromDafny_N6_simple__N9_resources__S24_SimpleResourcesException(dafnyVal);
                case Dafny.Simple.Resources.Types.Error_Opaque dafnyVal:
                    return new OpaqueError(dafnyVal._obj);
                default:
                    // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
                    return new OpaqueError();
            }
        }
        public static Dafny.Simple.Resources.Types._IError ToDafny_CommonError(System.Exception value)
        {
            switch (value)
            {
                case Simple.Resources.SimpleResourcesException exception:
                    return ToDafny_N6_simple__N9_resources__S24_SimpleResourcesException(exception);
                // OpaqueError is redundant, but listed for completeness.
                case OpaqueError exception:
                    return new Dafny.Simple.Resources.Types.Error_Opaque(exception);
                case System.Exception exception:
                    return new Dafny.Simple.Resources.Types.Error_Opaque(exception);
                default:
                    // The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)
                    return new Dafny.Simple.Resources.Types.Error_Opaque(value);
            }
        }
    }
}
