// Class SimpleConstraintsClient
// Dafny class SimpleConstraintsClient compiled into Java
package simple.constraints.internaldafny;

import simple.constraints.internaldafny.types.*;
import SimpleConstraintsImpl_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class SimpleConstraintsClient implements simple.constraints.internaldafny.types.ISimpleConstraintsClient {
  public SimpleConstraintsClient() {
    this._config = SimpleConstraintsImpl_Compile.Config.Default();
  }
  public void __ctor(SimpleConstraintsImpl_Compile.Config config)
  {
    (this)._config = config;
  }
  public Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> GetConstraints(simple.constraints.internaldafny.types.GetConstraintsInput input)
  {
    Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> output = Wrappers_Compile.Result.<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error>Default(simple.constraints.internaldafny.types.GetConstraintsOutput._typeDescriptor(), simple.constraints.internaldafny.types.Error._typeDescriptor(), simple.constraints.internaldafny.types.GetConstraintsOutput.Default());
    if(true) {
      Wrappers_Compile.Result<simple.constraints.internaldafny.types.GetConstraintsOutput, simple.constraints.internaldafny.types.Error> _out0;
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
  @Override
  public java.lang.String toString() {
    return "SimpleConstraints.SimpleConstraintsClient";
  }
}
