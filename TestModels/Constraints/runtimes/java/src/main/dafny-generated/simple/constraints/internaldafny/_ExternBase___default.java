// Class _ExternBase___default
// Dafny class __default compiled into Java
package simple.constraints.internaldafny;

import simple.constraints.internaldafny.types.*;
import SimpleConstraintsImpl_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class _ExternBase___default {
  public _ExternBase___default() {
  }
  public static simple.constraints.internaldafny.types.SimpleConstraintsConfig DefaultSimpleConstraintsConfig() {
    return simple.constraints.internaldafny.types.SimpleConstraintsConfig.create();
  }
  public static Wrappers_Compile.Result<SimpleConstraintsClient, simple.constraints.internaldafny.types.Error> SimpleConstraints(simple.constraints.internaldafny.types.SimpleConstraintsConfig config)
  {
    Wrappers_Compile.Result<SimpleConstraintsClient, simple.constraints.internaldafny.types.Error> res = (Wrappers_Compile.Result<SimpleConstraintsClient, simple.constraints.internaldafny.types.Error>)null;
    SimpleConstraintsClient _20_client;
    SimpleConstraintsClient _nw0 = new SimpleConstraintsClient();
    _nw0.__ctor(SimpleConstraintsImpl_Compile.Config.create());
    _20_client = _nw0;
    res = Wrappers_Compile.Result.<SimpleConstraintsClient, simple.constraints.internaldafny.types.Error>create_Success(((dafny.TypeDescriptor<SimpleConstraintsClient>)(java.lang.Object)dafny.TypeDescriptor.reference(SimpleConstraintsClient.class)), simple.constraints.internaldafny.types.Error._typeDescriptor(), _20_client);
    return res;
  }
  public static Wrappers_Compile.Result<simple.constraints.internaldafny.types.ISimpleConstraintsClient, simple.constraints.internaldafny.types.Error> CreateSuccessOfClient(simple.constraints.internaldafny.types.ISimpleConstraintsClient client) {
    return Wrappers_Compile.Result.<simple.constraints.internaldafny.types.ISimpleConstraintsClient, simple.constraints.internaldafny.types.Error>create_Success(((dafny.TypeDescriptor<simple.constraints.internaldafny.types.ISimpleConstraintsClient>)(java.lang.Object)dafny.TypeDescriptor.reference(simple.constraints.internaldafny.types.ISimpleConstraintsClient.class)), simple.constraints.internaldafny.types.Error._typeDescriptor(), client);
  }
  public static Wrappers_Compile.Result<simple.constraints.internaldafny.types.ISimpleConstraintsClient, simple.constraints.internaldafny.types.Error> CreateFailureOfError(simple.constraints.internaldafny.types.Error error) {
    return Wrappers_Compile.Result.<simple.constraints.internaldafny.types.ISimpleConstraintsClient, simple.constraints.internaldafny.types.Error>create_Failure(((dafny.TypeDescriptor<simple.constraints.internaldafny.types.ISimpleConstraintsClient>)(java.lang.Object)dafny.TypeDescriptor.reference(simple.constraints.internaldafny.types.ISimpleConstraintsClient.class)), simple.constraints.internaldafny.types.Error._typeDescriptor(), error);
  }
  @Override
  public java.lang.String toString() {
    return "SimpleConstraints._default";
  }
}
