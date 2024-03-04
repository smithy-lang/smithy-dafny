# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
import LanguageSpecificLogicImpl
import sys
import Wrappers
import _dafny

class default__(LanguageSpecificLogicImpl.default__):
    @staticmethod
    def GetPythonRuntimeVersion(config):
        return Wrappers.Result_Success(_dafny.Seq(str(sys.version)))

LanguageSpecificLogicImpl.default__ = default__