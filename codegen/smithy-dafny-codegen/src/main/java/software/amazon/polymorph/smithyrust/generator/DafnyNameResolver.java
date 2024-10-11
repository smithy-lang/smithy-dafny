package software.amazon.polymorph.smithyrust.generator;

public class DafnyNameResolver {

  public static String escapeName(String name) {
    if (name.equals("None")) {
      return "_None";
    }
    return name;
  }
}
