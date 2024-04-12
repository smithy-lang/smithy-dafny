// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.nativeWrapper;

class NativeWrapperCodegenTestConstants {

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

  static String CATCH_GENERAL =
    """
    catch (Exception e)
    {
        return Wrappers_Compile
            .Result<%s, test.foobar.internaldafny.types._IError>
            .create_Failure(TypeConversion.ToDafny_CommonError(e));
    }
    """; // Format: method name

  static String DO_OUTPUT =
    """
    public Wrappers_Compile._IResult<
        %s,
        test.foobar.internaldafny.types._IError
    > DoSomethingWithOutput()
    {
        %s
        try
        {
            %s nativeOutput = _impl.DoSomethingWithOutput();
            _ = nativeOutput ?? throw new FoobarServiceException(
                $"{_impl}._DoSomethingWithOutput returned null, should be {typeof(%s)}"
            );
            %s
            return Wrappers_Compile.Result<
                %s,
                test.foobar.internaldafny.types._IError
            >.create_Success(
                TypeConversion.%s(
                    nativeOutput)
            );
        }
        %s
    }

    public Wrappers_Compile._IResult<%s, test.foobar.internaldafny.types._IError>
        DoSomethingWithOutput_k()
    {
        throw new FoobarServiceException("Not supported at this time.");
    }
    """;

  static String getOutput(
    String abstractOutput,
    String validateOutputMethod,
    String nativeOutput,
    String invokeValidateOutput,
    String toDafnyOutputConverter,
    String catchGeneral
  ) {
    return DO_OUTPUT.formatted(
      abstractOutput,
      validateOutputMethod,
      nativeOutput,
      nativeOutput,
      invokeValidateOutput,
      abstractOutput,
      toDafnyOutputConverter,
      catchGeneral.formatted(abstractOutput),
      abstractOutput
    );
  }

  static String DO_OUTPUT_POSITIONAL = getOutput(
    "test.foobar.internaldafny.types.IThing", // abstract output or interface
    "", // validateOutput method
    "Test.Foobar.IThing", // type of native output
    "", // validate native output
    "ToDafny_N4_test__N6_foobar__S17_DoSomethingOutput", // to dafny output converter
    CATCH_GENERAL
  );

  static String DO_OUTPUT_NOT_POSITIONAL = getOutput(
    "test.foobar.internaldafny.types._IDoSomethingOutput",
    VALIDATE_NATIVE_OUTPUT.formatted(
      "Test.Foobar.DoSomethingOutput",
      "DoSomethingWithOutput"
    ),
    "Test.Foobar.DoSomethingOutput",
    "validateOutput(nativeOutput);",
    "ToDafny_N4_test__N6_foobar__S17_DoSomethingOutput", // to dafny output converter
    CATCH_GENERAL
  );

  static String DO_INPUT =
    """
    public Wrappers_Compile._IResult<
        _System._ITuple0,
        test.foobar.internaldafny.types._IError
    > DoSomethingWithInput(test.foobar.internaldafny.types._IDoSomethingInput input)
    {
        Test.Foobar.DoSomethingInput nativeInput =
            TypeConversion.FromDafny_N4_test__N6_foobar__S16_DoSomethingInput(
                input);
        try
        {
            _impl.DoSomethingWithInput(nativeInput);
            return Wrappers_Compile.Result<
                _System._ITuple0,
                test.foobar.internaldafny.types._IError
            >.create_Success(Tuple0.create());
        }
        %s
    }
    public Wrappers_Compile._IResult<_System._ITuple0, test.foobar.internaldafny.types._IError> DoSomethingWithInput_k(test.foobar.internaldafny.types._IDoSomethingInput input)
    {
        throw new FoobarServiceException("Not supported at this time.");
    }
    """.formatted(CATCH_GENERAL.formatted("_System._ITuple0"));

  static String DO =
    """
    public Wrappers_Compile._IResult<
        _System._ITuple0,
        test.foobar.internaldafny.types._IError
    > Do()
    {
        try
        {
            _impl.Do();
            return Wrappers_Compile.Result<
                _System._ITuple0,
                test.foobar.internaldafny.types._IError
            >.create_Success(Tuple0.create());
        }
        %s
    }

    public Wrappers_Compile._IResult<_System._ITuple0, test.foobar.internaldafny.types._IError> Do_k()
    {
        throw new FoobarServiceException("Not supported at this time.");
    }
    """.formatted(CATCH_GENERAL.formatted("_System._ITuple0"));

  static String CONSTRUCTOR =
    """
    public NativeWrapper_Baz(BazBase nativeImpl)
    {
        _impl = nativeImpl;
    }
    """;

  static String getNameSpacedNativeWrapper(
    String constructor,
    String operations
  ) {
    return """
    namespace Test.Foobar
    {
        internal class NativeWrapper_Baz : test.foobar.internaldafny.types.IBaz
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

  static String COMPLETE_CLASS = getNameSpacedNativeWrapper(
    CONSTRUCTOR,
    "%s\n%s".formatted(DO_INPUT, DO_OUTPUT_NOT_POSITIONAL)
  );

  static String PRELUDE =
    """
    // ReSharper disable RedundantUsingDirective
    // ReSharper disable RedundantNameQualifier
    // ReSharper disable SuggestVarOrType_SimpleTypes

    using System;
    using _System;
    using Wrappers_Compile;
    """;

  static String COMPLETE = "%s\n%s".formatted(PRELUDE, COMPLETE_CLASS);
}
