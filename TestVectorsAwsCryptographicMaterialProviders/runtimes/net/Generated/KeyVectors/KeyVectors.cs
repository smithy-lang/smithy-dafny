// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using AWS.Cryptography.MaterialProvidersTestVectorKeys;
 using software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types; namespace AWS.Cryptography.MaterialProvidersTestVectorKeys {
 public class KeyVectors {
 private readonly software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.IKeyVectorsClient _impl;
 public KeyVectors(software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.IKeyVectorsClient impl) {
    this._impl = impl;
}
 public software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types.IKeyVectorsClient impl() {
    return this._impl;
}
 public KeyVectors(AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyVectorsConfig input)
 {
 software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IKeyVectorsConfig internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N31_materialProvidersTestVectorKeys__S16_KeyVectorsConfig(input);
 var result = software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.__default.KeyVectors(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 this._impl = result.dtor_value;
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateTestVectorKeyring(AWS.Cryptography.MaterialProvidersTestVectorKeys.TestVectorKeyringInput input) {
 software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N31_materialProvidersTestVectorKeys__S22_TestVectorKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> result = _impl.CreateTestVectorKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProviders.IKeyring CreateWappedTestVectorKeyring(AWS.Cryptography.MaterialProvidersTestVectorKeys.TestVectorKeyringInput input) {
 software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ITestVectorKeyringInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N31_materialProvidersTestVectorKeys__S22_TestVectorKeyringInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types.IKeyring, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> result = _impl.CreateWappedTestVectorKeyring(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N17_materialProviders__S19_CreateKeyringOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProvidersTestVectorKeys.GetKeyDescriptionOutput GetKeyDescription(AWS.Cryptography.MaterialProvidersTestVectorKeys.GetKeyDescriptionInput input) {
 software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N31_materialProvidersTestVectorKeys__S22_GetKeyDescriptionInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IGetKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> result = _impl.GetKeyDescription(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N31_materialProvidersTestVectorKeys__S23_GetKeyDescriptionOutput(result.dtor_value);
}
 public AWS.Cryptography.MaterialProvidersTestVectorKeys.SerializeKeyDescriptionOutput SerializeKeyDescription(AWS.Cryptography.MaterialProvidersTestVectorKeys.SerializeKeyDescriptionInput input) {
 software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionInput internalInput = TypeConversion.ToDafny_N3_aws__N12_cryptography__N31_materialProvidersTestVectorKeys__S28_SerializeKeyDescriptionInput(input);
 Wrappers_Compile._IResult<software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._ISerializeKeyDescriptionOutput, software.amazon.cryptography.materialproviderstestvectorkeys.internaldafny.types._IError> result = _impl.SerializeKeyDescription(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N3_aws__N12_cryptography__N31_materialProvidersTestVectorKeys__S29_SerializeKeyDescriptionOutput(result.dtor_value);
}
}
}
