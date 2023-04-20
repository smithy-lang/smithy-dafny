// Class Error_SimpleResources
// Dafny class Error_SimpleResources compiled into Java
package Dafny.Simple.Dependencies.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public class Error_SimpleResources extends Error {
  public Dafny.Simple.Resources.Types.Error _SimpleResources;
  public Error_SimpleResources (Dafny.Simple.Resources.Types.Error SimpleResources) {
    this._SimpleResources = SimpleResources;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Error_SimpleResources o = (Error_SimpleResources)other;
    return true && java.util.Objects.equals(this._SimpleResources, o._SimpleResources);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 2;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._SimpleResources);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Dafny.Simple.Dependencies.Types_Compile.Error.SimpleResources");
    s.append("(");
    s.append(dafny.Helpers.toString(this._SimpleResources));
    s.append(")");
    return s.toString();
  }
}
