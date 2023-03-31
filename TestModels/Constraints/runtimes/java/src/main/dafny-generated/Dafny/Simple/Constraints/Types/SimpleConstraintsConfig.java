// Class SimpleConstraintsConfig
// Dafny class SimpleConstraintsConfig compiled into Java
package Dafny.Simple.Constraints.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public class SimpleConstraintsConfig {
  public SimpleConstraintsConfig () {
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    SimpleConstraintsConfig o = (SimpleConstraintsConfig)other;
    return true;
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Dafny.Simple.Constraints.Types_Compile.SimpleConstraintsConfig.SimpleConstraintsConfig");
    return s.toString();
  }

  private static final SimpleConstraintsConfig theDefault = Dafny.Simple.Constraints.Types.SimpleConstraintsConfig.create();
  public static SimpleConstraintsConfig Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<SimpleConstraintsConfig> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(SimpleConstraintsConfig.class, () -> Default());
  public static dafny.TypeDescriptor<SimpleConstraintsConfig> _typeDescriptor() {
    return (dafny.TypeDescriptor<SimpleConstraintsConfig>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static SimpleConstraintsConfig create() {
    return new SimpleConstraintsConfig();
  }
  public boolean is_SimpleConstraintsConfig() { return true; }
  public static java.util.ArrayList<SimpleConstraintsConfig> AllSingletonConstructors() {
    java.util.ArrayList<SimpleConstraintsConfig> singleton_iterator = new java.util.ArrayList<>();
    singleton_iterator.add(new SimpleConstraintsConfig());
    return singleton_iterator;
  }
}
