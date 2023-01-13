// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System.Linq; using System; namespace Example.Simpletypes {
 internal static class TypeConversion {
 public static Example.Simpletypes.EmptyConfig FromDafny_N7_example__N11_simpletypes__S11_EmptyConfig (Dafny.Example.Simpletypes.Types._IEmptyConfig value) {
 Dafny.Example.Simpletypes.Types.EmptyConfig concrete = (Dafny.Example.Simpletypes.Types.EmptyConfig)value; Example.Simpletypes.EmptyConfig converted = new Example.Simpletypes.EmptyConfig();  return converted;
}
 public static Dafny.Example.Simpletypes.Types._IEmptyConfig ToDafny_N7_example__N11_simpletypes__S11_EmptyConfig (Example.Simpletypes.EmptyConfig value) {

 return new Dafny.Example.Simpletypes.Types.EmptyConfig (  ) ;
}
 public static Example.Simpletypes.GetStringInput FromDafny_N7_example__N11_simpletypes__S14_GetStringInput (Dafny.Example.Simpletypes.Types._IGetStringInput value) {
 Dafny.Example.Simpletypes.Types.GetStringInput concrete = (Dafny.Example.Simpletypes.Types.GetStringInput)value; Example.Simpletypes.GetStringInput converted = new Example.Simpletypes.GetStringInput(); if (concrete._stringValue.is_Some) converted.StringValue = (string) FromDafny_N7_example__N11_simpletypes__S14_GetStringInput__M11_stringValue(concrete._stringValue); return converted;
}
 public static Dafny.Example.Simpletypes.Types._IGetStringInput ToDafny_N7_example__N11_simpletypes__S14_GetStringInput (Example.Simpletypes.GetStringInput value) {
 string var_stringValue = value.IsSetStringValue() ? value.StringValue : (string) null;
 return new Dafny.Example.Simpletypes.Types.GetStringInput ( ToDafny_N7_example__N11_simpletypes__S14_GetStringInput__M11_stringValue(var_stringValue) ) ;
}
 public static Example.Simpletypes.GetStringOutput FromDafny_N7_example__N11_simpletypes__S15_GetStringOutput (Dafny.Example.Simpletypes.Types._IGetStringOutput value) {
 Dafny.Example.Simpletypes.Types.GetStringOutput concrete = (Dafny.Example.Simpletypes.Types.GetStringOutput)value; Example.Simpletypes.GetStringOutput converted = new Example.Simpletypes.GetStringOutput(); if (concrete._result.is_Some) converted.Result = (string) FromDafny_N7_example__N11_simpletypes__S15_GetStringOutput__M6_result(concrete._result); return converted;
}
 public static Dafny.Example.Simpletypes.Types._IGetStringOutput ToDafny_N7_example__N11_simpletypes__S15_GetStringOutput (Example.Simpletypes.GetStringOutput value) {
 string var_result = value.IsSetResult() ? value.Result : (string) null;
 return new Dafny.Example.Simpletypes.Types.GetStringOutput ( ToDafny_N7_example__N11_simpletypes__S15_GetStringOutput__M6_result(var_result) ) ;
}
 public static string FromDafny_N7_example__N11_simpletypes__S14_GetStringInput__M11_stringValue (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
}
 public static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N7_example__N11_simpletypes__S14_GetStringInput__M11_stringValue (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string) value));
}
 public static string FromDafny_N7_example__N11_simpletypes__S15_GetStringOutput__M6_result (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
}
 public static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N7_example__N11_simpletypes__S15_GetStringOutput__M6_result (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string) value));
}
 public static string FromDafny_N6_smithy__N3_api__S6_String (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 public static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 public static System.Exception FromDafny_CommonError(Dafny.Example.Simpletypes.Types._IError value) {
 switch(value)
 {

 case Dafny.Example.Simpletypes.Types.Error_Opaque dafnyVal:
 return new OpaqueError(dafnyVal._obj);
 default:
 // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
 return new OpaqueError();
}
}
 public static Dafny.Example.Simpletypes.Types._IError ToDafny_CommonError(System.Exception value) {
 switch (value)
 {

 // OpaqueError is redundant, but listed for completeness.
 case OpaqueError exception:
 return new Dafny.Example.Simpletypes.Types.Error_Opaque(exception);
 case System.Exception exception:
 return new Dafny.Example.Simpletypes.Types.Error_Opaque(exception);
 default:
 // The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)
 return new Dafny.Example.Simpletypes.Types.Error_Opaque(value);
}
}
}
}
