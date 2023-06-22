# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.types.boolean.internaldafny.types
import simple_boolean.smithy_generated.simple_boolean.client as SimpleBoolean
import Wrappers_Compile
import asyncio
from simple_boolean.smithy_generated.simple_boolean.models import GetBooleanInput

class SimpleBooleanShim(simple.types.boolean.internaldafny.types.ISimpleTypesBooleanClient):
    def __init__(self, _impl: SimpleBoolean) :
        self._impl = _impl

    def GetBoolean(self, input: simple.types.boolean.internaldafny.types.GetBooleanInput_GetBooleanInput) -> simple.types.boolean.internaldafny.types.GetBooleanOutput_GetBooleanOutput:
        '''
        TODO: This is what this SHOULD look like after getting some sort of TypeConversion in
        unwrapped_request = TypeConversion.ToNative(input)
        try:
            wrapped_response = self._impl.get_boolean(unwrapped_request)
            return Wrappers_Compile.Result_Success(wrapped_response)
        catch ex:
            return Wrappers_Compile.Result_Failure(ex)
        '''

        unwrapped_request: GetBooleanInput = GetBooleanInput(value=input.value)
        wrapped_response = asyncio.run(self._impl.get_boolean(unwrapped_request))
        return Wrappers_Compile.Result_Success(wrapped_response)
