// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package SimpleExternV2Impl_Compile;

import Wrappers;
import simple.dafnyexternv2.internaldafny.types.GetExternV2Output;
import simple.dafnyexternv2.internaldafny.types.Error;
import SimpleExternV2Impl.Config;
import simple.dafnyexternv2.internaldafny.types.ExternV2MustErrorInput;
import simple.dafnyexternv2.internaldafny.types.GetExternV2Input;
import simple.dafnyexternv2.internaldafny.types.ExternV2MustErrorOutput;

// TODO: Complete implementation. https://sim.amazon.com/issues/CrypTool-5259
public class __default {
    public static Result<GetExternV2Output, Error> GetExternV2(Config config, GetExternV2Input input) {
        GetExternV2Output output = new GetExternV2Output(
                input._blobValue,
                input._booleanValue,
                input._stringValue,
                input._integerValue,
                input._longValue
        );
        return Result<GetExternV2Output, Error>.create_Success(output);
    }

    public static Result<ExternV2MustErrorOutput, Error> ExternV2MustError(Config config, ExternV2MustErrorInput input) {
        var exception = new Exception(
            simple.dafnyexternv2.ToNative.ExternV2MustErrorInput(input).value()
        );
        return Result<ExternV2MustErrorOutput, Error>.create_Failure(Error.create_Opaque(exception));
    }
}