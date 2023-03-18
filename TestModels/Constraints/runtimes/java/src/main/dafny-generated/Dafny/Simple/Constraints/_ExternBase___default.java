// Class _ExternBase___default
// Dafny class __default compiled into Java
package Dafny.Simple.Constraints;

import Dafny.Simple.Constraints.Types.*;
import SimpleConstraintsImpl_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class _ExternBase___default {
  public _ExternBase___default() {
  }
  public static Dafny.Simple.Constraints.Types.SimpleConstraintsConfig DefaultSimpleConstraintsConfig() {
    return Dafny.Simple.Constraints.Types.SimpleConstraintsConfig.create();
  }
  public static Wrappers_Compile.Result<SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> SimpleConstraints(Dafny.Simple.Constraints.Types.SimpleConstraintsConfig config)
  {
    Wrappers_Compile.Result<SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> res = (Wrappers_Compile.Result<SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error>)null;
    SimpleConstraintsClient _1_client;
    SimpleConstraintsClient _nw0 = new SimpleConstraintsClient();
    _nw0.__ctor(SimpleConstraintsImpl_Compile.Config.create());
    _1_client = _nw0;
    res = Wrappers_Compile.Result.<SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error>create_Success(_1_client);
    return res;
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "Dafny.Simple.Constraints_Compile._default";
  }
}
