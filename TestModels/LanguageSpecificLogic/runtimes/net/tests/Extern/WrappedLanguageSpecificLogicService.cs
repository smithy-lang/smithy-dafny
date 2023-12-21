// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Language.Specific.Logic;
using Language.Specific.Logic.Wrapped;
using TypeConversion = Language.Specific.Logic.TypeConversion ;
namespace language.specific.logic.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<types.ILanguageSpecificLogicClient, types._IError> WrappedLanguageSpecificLogic(types._ILanguageSpecificLogicConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N8_language__N8_specific__N5_logic__S27_LanguageSpecificLogicConfig(config);
            var impl = new LanguageSpecificLogic(wrappedConfig);
            var wrappedClient = new LanguageSpecificLogicShim(impl);
            return Result<types.ILanguageSpecificLogicClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
