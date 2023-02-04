// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System.Linq; using System; namespace Simple.Errors.Wrapped {
 public static class TypeConversion {
 internal static Simple.Errors.AlwaysErrorInput FromDafny_N6_simple__N6_errors__S16_AlwaysErrorInput (Dafny.Simple.Errors.Types._IAlwaysErrorInput value) {
 //Dafny.Simple.Errors.Types.AlwaysErrorInput concrete = (Dafny.Simple.Errors.Types.AlwaysErrorInput)value; Simple.Errors.AlwaysErrorInput converted = new Simple.Errors.AlwaysErrorInput(); if (concrete._value.is_Some) converted.Value = (Simple.Errors.SimpleErrorsException) FromDafny_N6_simple__N6_errors__S16_AlwaysErrorInput__M5_value(concrete._value); return converted;

    Dafny.Simple.Errors.Types.AlwaysErrorInput concrete =
  (Dafny.Simple.Errors.Types.AlwaysErrorInput)value; 
  Simple.Errors.AlwaysErrorInput converted = new Simple.Errors.AlwaysErrorInput();


   if (concrete._value.is_Some)  {
        Dafny.Simple.Errors.Types._IError newException = concrete._value.dtor_value;

        if (newException.is_SimpleErrorsException) {
        Dafny.Simple.Errors.Types.Error_SimpleErrorsException convertedThing = ( Dafny.Simple.Errors.Types.Error_SimpleErrorsException) newException;



        //Wrappers_Compile.Option_Some<Dafny.Simple.Errors.Types.Error_SimpleErrorsException>
        var
        optionWrappedConvertedThing = new 
        Wrappers_Compile.Option_Some<Dafny.Simple.Errors.Types.Error_SimpleErrorsException>(convertedThing);

           converted.Value = 
   (Simple.Errors.SimpleErrorsException) 
   FromDafny_N6_simple__N6_errors__S16_AlwaysErrorInput__M5_value(
    optionWrappedConvertedThing); 
    
             }
    }


    return converted;

}
 internal static Dafny.Simple.Errors.Types._IAlwaysErrorInput ToDafny_N6_simple__N6_errors__S16_AlwaysErrorInput (Simple.Errors.AlwaysErrorInput value) {
 Simple.Errors.SimpleErrorsException var_value = value.IsSetValue() ? value.Value : (Simple.Errors.SimpleErrorsException) null;
 return new Dafny.Simple.Errors.Types.AlwaysErrorInput ( ToDafny_N6_simple__N6_errors__S16_AlwaysErrorInput__M5_value(var_value) ) ;
}
 internal static Simple.Errors.AlwaysErrorOutput FromDafny_N6_simple__N6_errors__S17_AlwaysErrorOutput (Dafny.Simple.Errors.Types._IAlwaysErrorOutput value) {
 //Dafny.Simple.Errors.Types.AlwaysErrorOutput concrete = (Dafny.Simple.Errors.Types.AlwaysErrorOutput)value; Simple.Errors.AlwaysErrorOutput converted = new Simple.Errors.AlwaysErrorOutput(); if (concrete._value.is_Some) converted.Value = (Simple.Errors.SimpleErrorsException) FromDafny_N6_simple__N6_errors__S17_AlwaysErrorOutput__M5_value(concrete._value); return converted;

    Dafny.Simple.Errors.Types.AlwaysErrorOutput concrete =
  (Dafny.Simple.Errors.Types.AlwaysErrorOutput)value; 
  Simple.Errors.AlwaysErrorOutput converted = new Simple.Errors.AlwaysErrorOutput();


   if (concrete._value.is_Some)  {
        Dafny.Simple.Errors.Types._IError newException = concrete._value.dtor_value;

        if (newException.is_SimpleErrorsException) {
        Dafny.Simple.Errors.Types.Error_SimpleErrorsException convertedThing = ( Dafny.Simple.Errors.Types.Error_SimpleErrorsException) newException;



        //Wrappers_Compile.Option_Some<Dafny.Simple.Errors.Types.Error_SimpleErrorsException>
        var
        optionWrappedConvertedThing = new 
        Wrappers_Compile.Option_Some<Dafny.Simple.Errors.Types.Error_SimpleErrorsException>(convertedThing);

           converted.Value = 
   (Simple.Errors.SimpleErrorsException) 
   FromDafny_N6_simple__N6_errors__S17_AlwaysErrorOutput__M5_value(
    optionWrappedConvertedThing); 
    
             }
    }


    return converted;

}
 internal static Dafny.Simple.Errors.Types._IAlwaysErrorOutput ToDafny_N6_simple__N6_errors__S17_AlwaysErrorOutput (Simple.Errors.AlwaysErrorOutput value) {
 Simple.Errors.SimpleErrorsException var_value = value.IsSetValue() ? value.Value : (Simple.Errors.SimpleErrorsException) null;
 return new Dafny.Simple.Errors.Types.AlwaysErrorOutput ( ToDafny_N6_simple__N6_errors__S17_AlwaysErrorOutput__M5_value(var_value) ) ;
}
 internal static Simple.Errors.GetErrorsInput FromDafny_N6_simple__N6_errors__S14_GetErrorsInput (Dafny.Simple.Errors.Types._IGetErrorsInput value) {
 Dafny.Simple.Errors.Types.GetErrorsInput concrete = (Dafny.Simple.Errors.Types.GetErrorsInput)value; Simple.Errors.GetErrorsInput converted = new Simple.Errors.GetErrorsInput(); if (concrete._value.is_Some) converted.Value = (string) FromDafny_N6_simple__N6_errors__S14_GetErrorsInput__M5_value(concrete._value); return converted;
}
 internal static Dafny.Simple.Errors.Types._IGetErrorsInput ToDafny_N6_simple__N6_errors__S14_GetErrorsInput (Simple.Errors.GetErrorsInput value) {
 string var_value = value.IsSetValue() ? value.Value : (string) null;
 return new Dafny.Simple.Errors.Types.GetErrorsInput ( ToDafny_N6_simple__N6_errors__S14_GetErrorsInput__M5_value(var_value) ) ;
}
 internal static Simple.Errors.GetErrorsOutput FromDafny_N6_simple__N6_errors__S15_GetErrorsOutput (Dafny.Simple.Errors.Types._IGetErrorsOutput value) {
 Dafny.Simple.Errors.Types.GetErrorsOutput concrete = (Dafny.Simple.Errors.Types.GetErrorsOutput)value; Simple.Errors.GetErrorsOutput converted = new Simple.Errors.GetErrorsOutput(); if (concrete._value.is_Some) converted.Value = (string) FromDafny_N6_simple__N6_errors__S15_GetErrorsOutput__M5_value(concrete._value); return converted;
}
 internal static Dafny.Simple.Errors.Types._IGetErrorsOutput ToDafny_N6_simple__N6_errors__S15_GetErrorsOutput (Simple.Errors.GetErrorsOutput value) {
 string var_value = value.IsSetValue() ? value.Value : (string) null;
 return new Dafny.Simple.Errors.Types.GetErrorsOutput ( ToDafny_N6_simple__N6_errors__S15_GetErrorsOutput__M5_value(var_value) ) ;
}
 internal static Simple.Errors.SimpleErrorsConfig FromDafny_N6_simple__N6_errors__S18_SimpleErrorsConfig (Dafny.Simple.Errors.Types._ISimpleErrorsConfig value) {
 Dafny.Simple.Errors.Types.SimpleErrorsConfig concrete = (Dafny.Simple.Errors.Types.SimpleErrorsConfig)value; Simple.Errors.SimpleErrorsConfig converted = new Simple.Errors.SimpleErrorsConfig();  return converted;
}
 internal static Dafny.Simple.Errors.Types._ISimpleErrorsConfig ToDafny_N6_simple__N6_errors__S18_SimpleErrorsConfig (Simple.Errors.SimpleErrorsConfig value) {

 return new Dafny.Simple.Errors.Types.SimpleErrorsConfig (  ) ;
}
 internal static Simple.Errors.SimpleErrorsException FromDafny_N6_simple__N6_errors__S21_SimpleErrorsException (Dafny.Simple.Errors.Types.Error_SimpleErrorsException value) {
 return new Simple.Errors.SimpleErrorsException (
 FromDafny_N6_simple__N6_errors__S21_SimpleErrorsException__M7_message(value._message)
 ) ;
}
 internal static Dafny.Simple.Errors.Types.Error_SimpleErrorsException ToDafny_N6_simple__N6_errors__S21_SimpleErrorsException (Simple.Errors.SimpleErrorsException value) {

 return new Dafny.Simple.Errors.Types.Error_SimpleErrorsException (
 ToDafny_N6_simple__N6_errors__S21_SimpleErrorsException__M7_message(value.Message)
 ) ;
}
 internal static Simple.Errors.SimpleErrorsException FromDafny_N6_simple__N6_errors__S16_AlwaysErrorInput__M5_value (Wrappers_Compile._IOption<Dafny.Simple.Errors.Types.Error_SimpleErrorsException> value) {
 return value.is_None ? (Simple.Errors.SimpleErrorsException) null : FromDafny_N6_simple__N6_errors__S21_SimpleErrorsException(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.Simple.Errors.Types.Error_SimpleErrorsException> ToDafny_N6_simple__N6_errors__S16_AlwaysErrorInput__M5_value (Simple.Errors.SimpleErrorsException value) {
 return value == null ? Wrappers_Compile.Option<Dafny.Simple.Errors.Types.Error_SimpleErrorsException>.create_None() : Wrappers_Compile.Option<Dafny.Simple.Errors.Types.Error_SimpleErrorsException>.create_Some(ToDafny_N6_simple__N6_errors__S21_SimpleErrorsException((Simple.Errors.SimpleErrorsException) value));
}
 internal static Simple.Errors.SimpleErrorsException FromDafny_N6_simple__N6_errors__S17_AlwaysErrorOutput__M5_value (Wrappers_Compile._IOption<Dafny.Simple.Errors.Types.Error_SimpleErrorsException> value) {
 return value.is_None ? (Simple.Errors.SimpleErrorsException) null : FromDafny_N6_simple__N6_errors__S21_SimpleErrorsException(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.Simple.Errors.Types.Error_SimpleErrorsException> ToDafny_N6_simple__N6_errors__S17_AlwaysErrorOutput__M5_value (Simple.Errors.SimpleErrorsException value) {
 return value == null ? Wrappers_Compile.Option<Dafny.Simple.Errors.Types.Error_SimpleErrorsException>.create_None() : Wrappers_Compile.Option<Dafny.Simple.Errors.Types.Error_SimpleErrorsException>.create_Some(ToDafny_N6_simple__N6_errors__S21_SimpleErrorsException((Simple.Errors.SimpleErrorsException) value));
}
 internal static string FromDafny_N6_simple__N6_errors__S14_GetErrorsInput__M5_value (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N6_simple__N6_errors__S14_GetErrorsInput__M5_value (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string) value));
}
 internal static string FromDafny_N6_simple__N6_errors__S15_GetErrorsOutput__M5_value (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N6_simple__N6_errors__S15_GetErrorsOutput__M5_value (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string) value));
}
 internal static string FromDafny_N6_simple__N6_errors__S21_SimpleErrorsException__M7_message (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N6_simple__N6_errors__S21_SimpleErrorsException__M7_message (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N6_smithy__N3_api__S6_String (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 public static System.Exception FromDafny_CommonError(Dafny.Simple.Errors.Types._IError value) {
 switch(value)
 {
 case Dafny.Simple.Errors.Types.Error_SimpleErrorsException dafnyVal:
return FromDafny_N6_simple__N6_errors__S21_SimpleErrorsException(dafnyVal);
 case Dafny.Simple.Errors.Types.Error_Opaque dafnyVal:
 return new OpaqueError(dafnyVal._obj);
 default:
 // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
 return new OpaqueError();
}
}
 public static Dafny.Simple.Errors.Types._IError ToDafny_CommonError(System.Exception value) {
 switch (value)
 {
 case Simple.Errors.SimpleErrorsException exception:
 return ToDafny_N6_simple__N6_errors__S21_SimpleErrorsException(exception);
 // OpaqueError is redundant, but listed for completeness.
 case OpaqueError exception:
 return new Dafny.Simple.Errors.Types.Error_Opaque(exception);
 case System.Exception exception:
 return new Dafny.Simple.Errors.Types.Error_Opaque(exception);
 default:
 // The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)
 return new Dafny.Simple.Errors.Types.Error_Opaque(value);
}
}
}
}
