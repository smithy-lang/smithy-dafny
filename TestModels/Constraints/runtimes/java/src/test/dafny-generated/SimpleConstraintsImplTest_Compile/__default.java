// Class __default
// Dafny class __default compiled into Java
package SimpleConstraintsImplTest_Compile;

import Helpers_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void TestConstraints()
  {
    Dafny.Simple.Constraints.SimpleConstraintsClient _34_client;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _35_valueOrError0 = (Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _out4;
    _out4 = Dafny.Simple.Constraints.__default.SimpleConstraints(Dafny.Simple.Constraints.__default.DefaultSimpleConstraintsConfig());
    _35_valueOrError0 = _out4;
    if (!(!((_35_valueOrError0).IsFailure(Dafny.Simple.Constraints.SimpleConstraintsClient._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/polymorph/TestModels/Constraints/test/SimpleConstraintsImplTest.dfy(13,19): " + String.valueOf(_35_valueOrError0));
    }
    _34_client = (_35_valueOrError0).Extract(Dafny.Simple.Constraints.SimpleConstraintsClient._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor());
    __default.TestGetConstraintWithValidInputs(_34_client);
  }
  public static void TestGetConstraintWithValidInputs(Dafny.Simple.Constraints.Types.ISimpleConstraintsClient client)
  {
    Dafny.Simple.Constraints.Types.GetConstraintsInput _36_input;
    Dafny.Simple.Constraints.Types.GetConstraintsInput _out5;
    _out5 = Helpers_Compile.__default.GetConstraintsInputTemplate(dafny.DafnySet.<dafny.DafnySequence<? extends Character>> empty());
    _36_input = _out5;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error> _37_ret;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error> _out6;
    _out6 = (client).GetConstraints(_36_input);
    _37_ret = _out6;
    if (!((_37_ret).is_Success())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/polymorph/TestModels/Constraints/test/SimpleConstraintsImplTest.dfy(24,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "SimpleConstraintsImplTest_Compile._default";
  }
}
