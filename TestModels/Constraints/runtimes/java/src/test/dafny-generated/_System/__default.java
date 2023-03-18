// Class __default
// Dafny class __default compiled into Java
package _System;

import Helpers_Compile.*;
import SimpleConstraintsImplTest_Compile.*;
import Dafny.Simple.Constraints.Wrapped.*;
import WrappedSimpleConstraintsTest_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void Main(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> __noArgsParameter)
  {
    boolean _40_success;
    _40_success = true;
    System.out.print((dafny.DafnySequence.asString("SimpleConstraintsImplTest.TestConstraints: ")).verbatimString());
    try {
      {
        SimpleConstraintsImplTest_Compile.__default.TestConstraints();
        {
          System.out.print((dafny.DafnySequence.asString("PASSED\n")).verbatimString());
        }
      }
    }
    catch (dafny.DafnyHaltException e) {
      dafny.DafnySequence<Character> _41_haltMessage = dafny.DafnySequence.asString(e.getMessage());
      {
        System.out.print((dafny.DafnySequence.asString("FAILED\n	")).verbatimString());
        System.out.print(String.valueOf(_41_haltMessage));
        System.out.print((dafny.DafnySequence.asString("\n")).verbatimString());
        _40_success = false;
      }
    }
    System.out.print((dafny.DafnySequence.asString("WrappedSimpleConstraintsTest.GetConstraints: ")).verbatimString());
    try {
      {
        WrappedSimpleConstraintsTest_Compile.__default.GetConstraints();
        {
          System.out.print((dafny.DafnySequence.asString("PASSED\n")).verbatimString());
        }
      }
    }
    catch (dafny.DafnyHaltException e) {
      dafny.DafnySequence<Character> _42_haltMessage = dafny.DafnySequence.asString(e.getMessage());
      {
        System.out.print((dafny.DafnySequence.asString("FAILED\n	")).verbatimString());
        System.out.print(String.valueOf(_42_haltMessage));
        System.out.print((dafny.DafnySequence.asString("\n")).verbatimString());
        _40_success = false;
      }
    }
    if (!(_40_success)) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/polymorph/TestModels/Constraints/test/SimpleConstraintsImplTest.dfy(12,18): " + (dafny.DafnySequence.asString("Test failures occurred: see above.\n")).verbatimString());
    }
  }
  public static void __Main(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> args) {
    __default.Main(args);
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "_module._default";
  }
}
