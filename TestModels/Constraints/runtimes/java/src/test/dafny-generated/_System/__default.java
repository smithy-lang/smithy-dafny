// Class __default
// Dafny class __default compiled into Java
package _System;

import Helpers_Compile.*;
import SimpleConstraintsImplTest_Compile.*;
import simple.constraints.internaldafny.wrapped.*;
import WrappedSimpleConstraintsTest_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void __Test____Main__(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> __noArgsParameter)
  {
    boolean _255_success;
    _255_success = true;
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
      dafny.DafnySequence<Character> _256_haltMessage = dafny.DafnySequence.asString(e.getMessage());
      {
        System.out.print((dafny.DafnySequence.asString("FAILED\n	")).verbatimString());
        System.out.print((_256_haltMessage).verbatimString());
        System.out.print((dafny.DafnySequence.asString("\n")).verbatimString());
        _255_success = false;
      }
    }
    System.out.print((dafny.DafnySequence.asString("WrappedSimpleConstraintsTest.TestConstraints: ")).verbatimString());
    try {
      {
        WrappedSimpleConstraintsTest_Compile.__default.TestConstraints();
        {
          System.out.print((dafny.DafnySequence.asString("PASSED\n")).verbatimString());
        }
      }
    }
    catch (dafny.DafnyHaltException e) {
      dafny.DafnySequence<Character> _257_haltMessage = dafny.DafnySequence.asString(e.getMessage());
      {
        System.out.print((dafny.DafnySequence.asString("FAILED\n	")).verbatimString());
        System.out.print((_257_haltMessage).verbatimString());
        System.out.print((dafny.DafnySequence.asString("\n")).verbatimString());
        _255_success = false;
      }
    }
    if (!(_255_success)) {
      throw new dafny.DafnyHaltException("<stdin>(1,0): " + (dafny.DafnySequence.asString("Test failures occurred: see above.\n")).verbatimString());
    }
  }
  public static void __Main(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> args) {
    __default.__Test____Main__(args);
  }
  @Override
  public java.lang.String toString() {
    return "_module._default";
  }
}
