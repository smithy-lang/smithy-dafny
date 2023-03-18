// Class SimpleConstraintsClient
// Dafny class SimpleConstraintsClient compiled into Java
package Dafny.Simple.Constraints;

import Dafny.Simple.Constraints.Types.*;
import SimpleConstraintsImpl_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class SimpleConstraintsClient implements Dafny.Simple.Constraints.Types.ISimpleConstraintsClient {
  public SimpleConstraintsClient() {
    this._config = SimpleConstraintsImpl_Compile.Config.Default();
  }
  public void __ctor(SimpleConstraintsImpl_Compile.Config config)
  {
    (this)._config = config;
  }
  public Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error> GetConstraints(Dafny.Simple.Constraints.Types.GetConstraintsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error>Default(Dafny.Simple.Constraints.Types.GetConstraintsOutput.Default());
    if(true) {
      Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error> _out0;
      _out0 = SimpleConstraintsImpl_Compile.__default.GetConstraints((this).config(), input);
      output = _out0;
    }
    return output;
  }
  public SimpleConstraintsImpl_Compile.Config _config;
  public SimpleConstraintsImpl_Compile.Config config()
  {
    return this._config;
  }
  private static final dafny.TypeDescriptor<SimpleConstraintsClient> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(SimpleConstraintsClient.class, () -> (SimpleConstraintsClient) null);
  public static dafny.TypeDescriptor<SimpleConstraintsClient> _typeDescriptor() {
    return (dafny.TypeDescriptor<SimpleConstraintsClient>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "Dafny.Simple.Constraints_Compile.SimpleConstraintsClient";
  }
}
