package software.amazon.polymorph.smithygo.utils;

import software.amazon.smithy.model.shapes.MemberShape;

public class Constants {

  public static final String DAFNY_RUNTIME_GO_LIBRARY_MODULE =
    "github.com/dafny-lang/DafnyRuntimeGo/v4";

  // TODO: Is it possible to make this function name shorter and in camelCase?
  /**
   * Generates a function name for shape visitors for AWS SDK and localservice.
   *
   * @param memberShape The visiting MemberShape
   * @param suffix A string to be appended at the end of the generated function name
   * @return A string representing the generated function name
   */
  public static String funcNameGenerator(
    final MemberShape memberShape,
    final String suffix
  ) {
    return memberShape
      .getId()
      .toString()
      .replaceAll("[.$#]", "_")
      .concat("_")
      .concat(suffix);
  }
}
