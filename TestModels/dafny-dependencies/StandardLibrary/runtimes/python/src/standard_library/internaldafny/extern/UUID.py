# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
import uuid

import Wrappers
import _dafny
from standard_library.internaldafny.generated.UUID import *
import standard_library.internaldafny.generated.UUID

class default__:
    @staticmethod
    def ToByteArray(dafny_str):
        try:
            uuid_from_str = uuid.UUID(''.join(dafny_str.Elements))
            return Wrappers.Result_Success(_dafny.Seq(uuid_from_str.bytes))
        except Exception as e:
            return Wrappers.Result_Failure(_dafny.string_of(
                "Could not convert UUID to byte array: " + str(e)
            ))
        
    @staticmethod
    def FromByteArray(dafny_b):
        try:
            native_bytes = bytes(dafny_b.Elements)
            uuid_from_bytes = uuid.UUID(bytes=native_bytes)
            return Wrappers.Result_Success(_dafny.Seq(str(uuid_from_bytes)))
        except Exception as e:
            return Wrappers.Result_Failure(_dafny.string_of(
                "Could not convert byte array to UUID: " + str(e)
            ))

    @staticmethod
    def GenerateUUID():
        try:
            generated_uuid = uuid.uuid4()
            return Wrappers.Result_Success(_dafny.Seq(str(generated_uuid)))
        except Exception as e:
            return Wrappers.Result_Failure(_dafny.Seq("Could not generate a UUID: " + str(e)))

standard_library.internaldafny.generated.UUID.default__ = default__