// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
using Dafny;
using simple.dafnyextern.internaldafny.types;
using Simple.DafnyExtern;
using Wrappers_Compile;
using GetExternOutput = simple.dafnyextern.internaldafny.types.GetExternOutput;

namespace SimpleExternImpl_Compile
{
    public partial class __default
    {
        public static _IResult<_IGetExternOutput, _IError> GetExtern(_IConfig config, _IGetExternInput input)
        {
            var output = new GetExternOutput(input.dtor_blobValue,
                input.dtor_booleanValue,
                input.dtor_stringValue,
                input.dtor_integerValue,
                input.dtor_longValue);
            return Result<_IGetExternOutput, _IError>.create_Success(output);
        }

        public static _IResult<_IExternMustErrorOutput, _IError> ExternMustError(_IConfig config,
            _IExternMustErrorInput input)
        {
            var exception = new Exception(
                TypeConversion
                    .FromDafny_N6_simple__N11_dafnyExtern__S20_ExternMustErrorInput__M5_value(input.dtor_value));
            return Result<_IExternMustErrorOutput, _IError>.create_Failure(Error.create_Opaque(exception));
        }
    }
}

namespace ExternConstructor
{
    public class ExternConstructorClass
    {
        private readonly string inputVal;

        // C# constructor can throw error. In these cases, dafny would halt the whole program
        // since constructor can't have a return type and can't return the error to dafny.
        private ExternConstructorClass(string input)
        {
            // This is to test the constructor error scenario.
            if ("Error".Equals(input, StringComparison.InvariantCultureIgnoreCase))
                throw new Exception("Constructor Exception");
            inputVal = input;
        }

        // This method is used to create and return an instance of the class or any associated exceptions.
        public static _IResult<ExternConstructorClass, _IError> Build(ISequence<char> input)
        {
            try
            {
                return Result<ExternConstructorClass, _IError>.create_Success(
                    new ExternConstructorClass(TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(input)));
            }
            catch (Exception ex)
            {
                return Result<ExternConstructorClass, _IError>.create_Failure(Error.create_Opaque(ex));
            }
        }

        public _IResult<ISequence<char>, _IError> GetValue()
        {
            return Result<ISequence<char>, _IError>.create_Success(
                TypeConversion.ToDafny_N6_smithy__N3_api__S6_String(inputVal));
        }
    }
}
