# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from language_specific_logic.smithygenerated.language_specific_logic.client import LanguageSpecificLogic
from language_specific_logic.smithygenerated.language_specific_logic.shim import LanguageSpecificLogicShim
from language_specific_logic.smithygenerated.language_specific_logic.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedLanguageSpecificLogicService

class default__(WrappedLanguageSpecificLogicService.default__):

    @staticmethod
    def WrappedLanguageSpecificLogic(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = LanguageSpecificLogic(wrapped_config)
        wrapped_client = LanguageSpecificLogicShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedLanguageSpecificLogicService.default__ = default__
