// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using Example.Simpletypes;
 using Dafny.Example.Simpletypes.Types; namespace Example.Simpletypes {
 public class SimpleTypes {
 private readonly ISimpleTypesServiceClient _impl;
 public SimpleTypes(Example.Simpletypes.EmptyConfig input)
 {
 Dafny.Example.Simpletypes.Types._IEmptyConfig internalInput = TypeConversion.ToDafny_N7_example__N11_simpletypes__S11_EmptyConfig(input);
 var result = Dafny.Example.Simpletypes.__default.SimpleTypes(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 this._impl = result.dtor_value;
}
 public Example.Simpletypes.GetStringOutput GetString(Example.Simpletypes.GetStringInput input) {
 Dafny.Example.Simpletypes.Types._IGetStringInput internalInput = TypeConversion.ToDafny_N7_example__N11_simpletypes__S14_GetStringInput(input);
 Wrappers_Compile._IResult<Dafny.Example.Simpletypes.Types._IGetStringOutput, Dafny.Example.Simpletypes.Types._IError> result = (Wrappers_Compile._IResult<Dafny.Example.Simpletypes.Types._IGetStringOutput, Dafny.Example.Simpletypes.Types._IError>)_impl.GetString(internalInput.dtor_stringValue);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N7_example__N11_simpletypes__S15_GetStringOutput(result.dtor_value);
}
}
}
