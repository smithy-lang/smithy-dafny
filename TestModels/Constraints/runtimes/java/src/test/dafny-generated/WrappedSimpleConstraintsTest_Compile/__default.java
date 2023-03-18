// Class __default
// Dafny class __default compiled into Java
package WrappedSimpleConstraintsTest_Compile;

import Helpers_Compile.*;
import SimpleConstraintsImplTest_Compile.*;
import Dafny.Simple.Constraints.Wrapped.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void GetConstraints()
  {
    Dafny.Simple.Constraints.Types.ISimpleConstraintsClient _38_client;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _39_valueOrError0 = (Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _out7;
    _out7 = Dafny.Simple.Constraints.Wrapped.__default.WrappedSimpleConstraints(Dafny.Simple.Constraints.Wrapped.__default.WrappedDefaultSimpleConstraintsConfig());
    _39_valueOrError0 = _out7;
    if (!(!((_39_valueOrError0).IsFailure(Dafny.Simple.Constraints.Types._Companion_ISimpleConstraintsClient._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/polymorph/TestModels/Constraints/test/WrappedSimpleConstraintsTest.dfy(9,19): " + String.valueOf(_39_valueOrError0));
    }
    _38_client = (_39_valueOrError0).Extract(Dafny.Simple.Constraints.Types._Companion_ISimpleConstraintsClient._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor());
    SimpleConstraintsImplTest_Compile.__default.TestGetConstraintWithValidInputs(_38_client);
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "WrappedSimpleConstraintsTest_Compile._default";
  }
}
