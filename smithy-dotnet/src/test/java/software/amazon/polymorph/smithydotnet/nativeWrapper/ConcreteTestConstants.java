package software.amazon.polymorph.smithydotnet.nativeWrapper;

class ConcreteTestConstants {

    static String CATCH_SERVICE_DO_OUTPUT =
            """
            catch (FoobarServiceBaseException e)
            {
                return Wrappers_Compile.Result<
                    Dafny.Test.Foobar._IDoSomethingOutput,
                    Dafny.Test.Foobar.IFoobarServiceException
                >.create_Failure(
                    TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(e)
                );
            }
            """;

    static String CATCH_GENERAL_DO_OUTPUT =
            """
            catch (Exception e)
            {
                return Wrappers_Compile.Result<
                    Dafny.Test.Foobar._IDoSomethingOutput,
                    Dafny.Test.Foobar.IFoobarServiceException
                >.create_Failure(
                    TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(
                        new FoobarServiceBaseException(e.Message))
                );
            }
            """;

    static String CATCH_SERVICE_DO_VOID =
            """
            catch (FoobarServiceBaseException e)
            {
                return Wrappers_Compile.Result<
                    _System._ITuple0,
                    Dafny.Test.Foobar.IFoobarServiceException
                >.create_Failure(
                    TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(e)
                );
            }
            """;

    static String CATCH_GENERAL_DO_VOID =
            """
            catch (Exception e)
            {
                return Wrappers_Compile.Result<
                    _System._ITuple0,
                    Dafny.Test.Foobar.IFoobarServiceException
                >.create_Failure(
                    TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(
                        new FoobarServiceBaseException(e.Message))
                );
            }
            """;

    static String DO_OUTPUT =
            """
            public override Wrappers_Compile._IResult<
                Dafny.Test.Foobar._IDoSomethingOutput,
                Dafny.Test.Foobar.IFoobarServiceException
            > DoSomethingWithOutput()
            {
                try
                {
                    // ReSharper disable once RedundantNameQualifier
                    Test.Foobar.DoSomethingOutput nativeOutput = _impl.DoSomethingWithOutput();
                    return Wrappers_Compile.Result<
                        Dafny.Test.Foobar._IDoSomethingOutput,
                        Dafny.Test.Foobar.IFoobarServiceException
                    >.create_Success(
                        TypeConversion.ToDafny_N4_test__N6_foobar__S17_DoSomethingOutput(
                            nativeOutput)
                    );
                }
                %s
                %s
            }
            """.formatted(
                    CATCH_SERVICE_DO_OUTPUT,
                    CATCH_GENERAL_DO_OUTPUT
            );

    static String DO_INPUT =
            """
            public override Wrappers_Compile._IResult<
                _System._ITuple0,
                Dafny.Test.Foobar.IFoobarServiceException
            > DoSomethingWithInput(Dafny.Test.Foobar._IDoSomethingInput input)
            {
                // ReSharper disable once RedundantNameQualifier
                Test.Foobar.DoSomethingInput nativeInput =
                    TypeConversion.FromDafny_N4_test__N6_foobar__S16_DoSomethingInput(
                        input);
                try
                {
                    _impl.DoSomethingWithInput(nativeInput);
                    return Wrappers_Compile.Result<
                        _System._ITuple0,
                        Dafny.Test.Foobar.IFoobarServiceException
                    >.create_Success();
                }
                %s
                %s
            }
            """.formatted(CATCH_SERVICE_DO_VOID, CATCH_GENERAL_DO_VOID);

    static String DO =
            """
            public override Wrappers_Compile._IResult<
                _System._ITuple0,
                Dafny.Test.Foobar.IFoobarServiceException
            > Do()
            {
                try
                {
                    _impl.Do();
                    return Wrappers_Compile.Result<
                        _System._ITuple0,
                        Dafny.Test.Foobar.IFoobarServiceException
                    >.create_Success();
                }
                %s
                %s
            }
            """.formatted(CATCH_SERVICE_DO_VOID, CATCH_GENERAL_DO_VOID);

    static String CONSTRUCTOR =
            """
            public NativeWrapper_Baz(BazBase nativeImpl)
            {
                _impl = nativeImpl;
            }
            """;

    static String getNameSpacedNativeWrapper(String constructor, String operations) {
        return
        """
        namespace Test.Foobar
        {
            internal class NativeWrapper_Baz : Dafny.Test.Foobar.IBaz
            {
                internal readonly BazBase _impl;
                    
                %s
                
                %s
            }
        }
        """.formatted(constructor, operations);
    }

    static String SIMPLE_CLASS = getNameSpacedNativeWrapper(CONSTRUCTOR, "");

    static String VOID_CLASS = getNameSpacedNativeWrapper(CONSTRUCTOR, DO);

    static String COMPLETE_CLASS =
            getNameSpacedNativeWrapper(
                    CONSTRUCTOR,
                    "%s\n%s".formatted(DO_INPUT, DO_OUTPUT));

    static String PRELUDE =
            """
            // Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
            // SPDX-License-Identifier: Apache-2.0
            // Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
                        
            // ReSharper disable thrice RedundantUsingDirective
            using System;
            using AWS.EncryptionSDK.Core;
            using Wrappers_Compile;
            """;

    static String COMPLETE =
            "%s\n%s".formatted(PRELUDE, COMPLETE_CLASS);
}
