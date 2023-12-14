// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
using Dafny;
using simple.dafnyexternv2.internaldafny.types;
using Simple.DafnyExternV2;
using outer.Wrappers;
using GetExternV2Output = simple.dafnyexternv2.internaldafny.types.GetExternV2Output;

namespace SimpleExternV2Impl_Compile
{
    public partial class __default
    {
        public static _IResult<_IGetExternV2Output, _IError> GetExternV2(_IConfig config, _IGetExternV2Input input)
        {
            var output = new GetExternV2Output(input.dtor_blobValue,
                input.dtor_booleanValue,
                input.dtor_stringValue,
                input.dtor_integerValue,
                input.dtor_longValue);
            return Result<_IGetExternV2Output, _IError>.create_Success(output);
        }

        public static _IResult<_IExternV2MustErrorOutput, _IError> ExternV2MustError(_IConfig config,
            _IExternV2MustErrorInput input)
        {
            var exception = new Exception(
                TypeConversion
                    .FromDafny_N6_simple__N13_dafnyExternV2__S22_ExternV2MustErrorInput__M5_value(input.dtor_value));
            return Result<_IExternV2MustErrorOutput, _IError>.create_Failure(Error.create_Opaque(exception));
        }
    }
}

namespace ExternV2Constructor
{
    public class ExternV2ConstructorClass
    {
        private readonly string inputVal;

        // C# constructor can throw error. In these cases, dafny would halt the whole program
        // since constructor can't have a return type and can't return the error to dafny.
        private ExternV2ConstructorClass(string input)
        {
            // This is to test the constructor error scenario.
            if ("Error".Equals(input, StringComparison.InvariantCultureIgnoreCase))
                throw new Exception("Constructor Exception");
            inputVal = input;
        }

        // This method is used to create and return an instance of the class or any associated exceptions.
        public static _IResult<ExternV2ConstructorClass, _IError> Build(ISequence<char> input)
        {
            try
            {
                return Result<ExternV2ConstructorClass, _IError>.create_Success(
                    new ExternV2ConstructorClass(TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(input)));
            }
            catch (Exception ex)
            {
                return Result<ExternV2ConstructorClass, _IError>.create_Failure(Error.create_Opaque(ex));
            }
        }

        public _IResult<ISequence<char>, _IError> GetValue()
        {
            return Result<ISequence<char>, _IError>.create_Success(
                TypeConversion.ToDafny_N6_smithy__N3_api__S6_String(inputVal));
        }
    }
}
