// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using System;
using Dafny;
using language.specific.logic.internaldafny.types;
using Language.Specific.Logic;
using Wrappers_Compile;

namespace smithydafny.net.externs
{
  public partial class __default
  {
    public static Wrappers_Compile._IResult<
        Dafny.ISequence<char>,
        language.specific.logic.internaldafny.types._IError>
      getnetlanguage (
        smithydafny.net.externs._IConfig config
    ) {
      return Wrappers_Compile.Result<
        Dafny.ISequence<char>,
        language.specific.logic.internaldafny.types._IError
      >.create_Success(
        Dafny.Sequence<char>.FromString(
            System.Environment.Version.ToString()
          )
      );
    }
  }
}
