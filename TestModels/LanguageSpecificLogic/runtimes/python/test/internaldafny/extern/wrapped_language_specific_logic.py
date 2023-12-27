# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import language_specific_logic_internaldafny_wrapped
from language_specific_logic.smithygenerated.language_specific_logic.client import LanguageSpecificLogic
from language_specific_logic.smithygenerated.language_specific_logic.shim import LanguageSpecificLogicShim
from language_specific_logic.smithygenerated.language_specific_logic.config import dafny_config_to_smithy_config
import Wrappers

class default__(language_specific_logic_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedLanguageSpecificLogic(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = LanguageSpecificLogic(wrapped_config)
        wrapped_client = LanguageSpecificLogicShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
language_specific_logic_internaldafny_wrapped.default__ = default__
