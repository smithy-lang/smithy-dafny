// Class __default
// Dafny class __default compiled into Java
package _System;

import Dafny.Simple.Dependencies.Wrapped.*;
import Helpers_Compile.*;
import SimpleDependenciesImplTest_Compile.*;
import WrappedSimpleDependenciesTest_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void __Test____Main__(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> __noArgsParameter)
  {
    boolean _72_success;
    _72_success = true;
    System.out.print((dafny.DafnySequence.asString("SimpleDependenciesImplTest.TestDependenciesWithDefaultConfig: ")).verbatimString());
    try {
      {
        SimpleDependenciesImplTest_Compile.__default.TestDependenciesWithDefaultConfig();
        {
          System.out.print((dafny.DafnySequence.asString("PASSED\n")).verbatimString());
        }
      }
    }
    catch (dafny.DafnyHaltException e) {
      dafny.DafnySequence<Character> _73_haltMessage = dafny.DafnySequence.asString(e.getMessage());
      {
        System.out.print((dafny.DafnySequence.asString("FAILED\n	")).verbatimString());
        System.out.print((_73_haltMessage).verbatimString());
        System.out.print((dafny.DafnySequence.asString("\n")).verbatimString());
        _72_success = false;
      }
    }
    System.out.print((dafny.DafnySequence.asString("SimpleDependenciesImplTest.TestDependenciesWithCustomConfig: ")).verbatimString());
    try {
      {
        SimpleDependenciesImplTest_Compile.__default.TestDependenciesWithCustomConfig();
        {
          System.out.print((dafny.DafnySequence.asString("PASSED\n")).verbatimString());
        }
      }
    }
    catch (dafny.DafnyHaltException e) {
      dafny.DafnySequence<Character> _74_haltMessage = dafny.DafnySequence.asString(e.getMessage());
      {
        System.out.print((dafny.DafnySequence.asString("FAILED\n	")).verbatimString());
        System.out.print((_74_haltMessage).verbatimString());
        System.out.print((dafny.DafnySequence.asString("\n")).verbatimString());
        _72_success = false;
      }
    }
    System.out.print((dafny.DafnySequence.asString("WrappedSimpleDependenciesTest.TestDependenciesWithDefaultConfig: ")).verbatimString());
    try {
      {
        WrappedSimpleDependenciesTest_Compile.__default.TestDependenciesWithDefaultConfig();
        {
          System.out.print((dafny.DafnySequence.asString("PASSED\n")).verbatimString());
        }
      }
    }
    catch (dafny.DafnyHaltException e) {
      dafny.DafnySequence<Character> _75_haltMessage = dafny.DafnySequence.asString(e.getMessage());
      {
        System.out.print((dafny.DafnySequence.asString("FAILED\n	")).verbatimString());
        System.out.print((_75_haltMessage).verbatimString());
        System.out.print((dafny.DafnySequence.asString("\n")).verbatimString());
        _72_success = false;
      }
    }
    System.out.print((dafny.DafnySequence.asString("WrappedSimpleDependenciesTest.TestDependenciesWithCustomConfig: ")).verbatimString());
    try {
      {
        WrappedSimpleDependenciesTest_Compile.__default.TestDependenciesWithCustomConfig();
        {
          System.out.print((dafny.DafnySequence.asString("PASSED\n")).verbatimString());
        }
      }
    }
    catch (dafny.DafnyHaltException e) {
      dafny.DafnySequence<Character> _76_haltMessage = dafny.DafnySequence.asString(e.getMessage());
      {
        System.out.print((dafny.DafnySequence.asString("FAILED\n	")).verbatimString());
        System.out.print((_76_haltMessage).verbatimString());
        System.out.print((dafny.DafnySequence.asString("\n")).verbatimString());
        _72_success = false;
      }
    }
    if (!(_72_success)) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/WrappedSimpleDependenciesTest.dfy(1,0): " + (dafny.DafnySequence.asString("Test failures occurred: see above.\n")).verbatimString());
    }
  }
  public static void __Main(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> args) {
    __default.__Test____Main__(args);
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
