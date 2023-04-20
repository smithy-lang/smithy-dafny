// Class Error_SimpleConstraints
// Dafny class Error_SimpleConstraints compiled into Java
package Dafny.Simple.Dependencies.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public class Error_SimpleConstraints extends Error {
  public Dafny.Simple.Constraints.Types.Error _SimpleConstraints;
  public Error_SimpleConstraints (Dafny.Simple.Constraints.Types.Error SimpleConstraints) {
    this._SimpleConstraints = SimpleConstraints;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Error_SimpleConstraints o = (Error_SimpleConstraints)other;
    return true && java.util.Objects.equals(this._SimpleConstraints, o._SimpleConstraints);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._SimpleConstraints);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Dafny.Simple.Dependencies.Types_Compile.Error.SimpleConstraints");
    s.append("(");
    s.append(dafny.Helpers.toString(this._SimpleConstraints));
    s.append(")");
    return s.toString();
  }
}
