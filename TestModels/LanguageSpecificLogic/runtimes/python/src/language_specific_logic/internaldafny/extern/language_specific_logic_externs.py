# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
import _dafny
import sys

import language_specific_logic.internaldafny.generated.LanguageSpecificLogicImpl as LanguageSpecificLogicImpl
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

class default__(LanguageSpecificLogicImpl.default__):
    @staticmethod
    def GetPythonRuntimeVersion(config):
        return Wrappers.Result_Success(_dafny.Seq(str(sys.version)))

LanguageSpecificLogicImpl.default__ = default__