// Class Error_SimpleExtendableResources
// Dafny class Error_SimpleExtendableResources compiled into Java
package Dafny.Simple.Dependencies.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public class Error_SimpleExtendableResources extends Error {
  public Dafny.Simple.Extendable.Resources.Types.Error _SimpleExtendableResources;
  public Error_SimpleExtendableResources (Dafny.Simple.Extendable.Resources.Types.Error SimpleExtendableResources) {
    this._SimpleExtendableResources = SimpleExtendableResources;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Error_SimpleExtendableResources o = (Error_SimpleExtendableResources)other;
    return true && java.util.Objects.equals(this._SimpleExtendableResources, o._SimpleExtendableResources);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 1;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._SimpleExtendableResources);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Dafny.Simple.Dependencies.Types_Compile.Error.SimpleExtendableResources");
    s.append("(");
    s.append(dafny.Helpers.toString(this._SimpleExtendableResources));
    s.append(")");
    return s.toString();
  }
}
