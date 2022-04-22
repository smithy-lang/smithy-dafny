// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.nativeWrapper;

class ConcreteNativeWrapperTestConstants {

    static String VALIDATE_NATIVE_OUTPUT =
            """
            void validateOutput(%s nativeOutput)
            {
                try { nativeOutput.Validate(); } catch (ArgumentException e)
                {
                    var message = $"Output of {_impl}._%s is invalid. {e.Message}";
                    throw new FoobarServiceException(message);
                }
            }
            """; // Format: nativeOutputType, methodName

    static String RETURN_FAILURE =
            """
            return Wrappers_Compile.Result<
                %s,
                Dafny.Test.Foobar.IFoobarServiceException
            >.create_Failure(
                TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(finalException)
            );
            """; // Format: dafnyOutputType

    static String CATCH_SERVICE =
            """
            catch (FoobarServiceException e)
            {
                finalException = e;
            }
            """;

    static String CATCH_GENERAL =
            """
            catch (Exception e)
            {
                finalException = new %s(e.Message);
            }
            """.formatted("FoobarServiceException");

    static String DO_OUTPUT =
            """
            public Wrappers_Compile._IResult<
                %s,
                Dafny.Test.Foobar.IFoobarServiceException
            > DoSomethingWithOutput()
            {
                %s
                FoobarServiceException finalException = null;
                try
                {
                    %s nativeOutput = _impl.DoSomethingWithOutput();
                    _ = nativeOutput ?? throw new FoobarServiceException(
                        $"Output of {_impl}._DoSomethingWithOutput is invalid. " +
                        $"Should be {typeof(%s)} but is null."
                    );
                    %s
                    return Wrappers_Compile.Result<
                        %s,
                        Dafny.Test.Foobar.IFoobarServiceException
                    >.create_Success(
                        TypeConversion.%s(
                            nativeOutput)
                    );
                }
                %s
                %s
                %s
            }
            """;

    static String DO_OUTPUT_POSITIONAL = DO_OUTPUT.formatted(
            "Dafny.Test.Foobar.IThing", // abstract output or interface
            "", // validateOutput method
            "Test.Foobar.IThing", // type of native output
            "Test.Foobar.IThing", // type of native output
            "", // validate native output
            "Dafny.Test.Foobar.IThing", // abstract output or interface
            "ToDafny_N4_test__N6_foobar__S17_DoSomethingOutput", // to dafny output converter
            CATCH_SERVICE,
            CATCH_GENERAL,
            RETURN_FAILURE.formatted("Dafny.Test.Foobar.IThing")// return failure
    );

    static String DO_OUTPUT_NOT_POSITIONAL = DO_OUTPUT.formatted(
            "Dafny.Test.Foobar._IDoSomethingOutput",
            VALIDATE_NATIVE_OUTPUT.formatted("Test.Foobar.DoSomethingOutput", "DoSomethingWithOutput"),
            "Test.Foobar.DoSomethingOutput",
            "Test.Foobar.DoSomethingOutput",
            "validateOutput(nativeOutput);",
            "Dafny.Test.Foobar._IDoSomethingOutput",
            "ToDafny_N4_test__N6_foobar__S17_DoSomethingOutput", // to dafny output converter
            CATCH_SERVICE,
            CATCH_GENERAL,
            RETURN_FAILURE.formatted("Dafny.Test.Foobar._IDoSomethingOutput")// return failure
    );

    static String DO_INPUT =
            """
            public Wrappers_Compile._IResult<
                _System._ITuple0,
                Dafny.Test.Foobar.IFoobarServiceException
            > DoSomethingWithInput(Dafny.Test.Foobar._IDoSomethingInput input)
            {
                Test.Foobar.DoSomethingInput nativeInput =
                    TypeConversion.FromDafny_N4_test__N6_foobar__S16_DoSomethingInput(
                        input);
                FoobarServiceException finalException = null;
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
                %s
            }
            """.formatted(CATCH_SERVICE, CATCH_GENERAL, RETURN_FAILURE.formatted("_System._ITuple0"));

    static String DO =
            """
            public Wrappers_Compile._IResult<
                _System._ITuple0,
                Dafny.Test.Foobar.IFoobarServiceException
            > Do()
            {
                FoobarServiceException finalException = null;
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
                %s
            }
            """.formatted(CATCH_SERVICE, CATCH_GENERAL, RETURN_FAILURE.formatted("_System._ITuple0"));

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
                    "%s\n%s".formatted(DO_INPUT, DO_OUTPUT_NOT_POSITIONAL));

    static String PRELUDE =
            """                        
            // ReSharper disable RedundantUsingDirective
            // ReSharper disable RedundantNameQualifier
            // ReSharper disable SuggestVarOrType_SimpleTypes
            
            using System;
            using AWS.EncryptionSDK.Core;
            using Wrappers_Compile;
            """;

    static String COMPLETE =
            "%s\n%s".formatted(PRELUDE, COMPLETE_CLASS);
}
