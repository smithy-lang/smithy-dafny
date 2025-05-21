package software.amazon.polymorph.smithygo.utils;

import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.utils.StringUtils;

public class Constants {

  public static final String DAFNY_RUNTIME_GO_LIBRARY_MODULE =
    "github.com/dafny-lang/DafnyRuntimeGo/v4";
  public static final String SMITHY_DAFNY_STD_LIB_GO =
    "github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library";

  // TODO: Is it possible to make this function name shorter and in camelCase?
  /**
   * Generates a function name used for type conversion of memberShapes.
   * Always generates public (exported) function for all shape
   *
   * @param memberShape The visiting MemberShape
   * @param suffix A string to be appended at the end of the generated function name
   * @return A string representing the generated function name
   */
  public static String funcNameGenerator(
    final MemberShape memberShape,
    final String suffix
  ) {
    return StringUtils.capitalize(
      memberShape
        .getId()
        .toString()
        .replaceAll("[.$#]", "_")
        .concat("_")
        .concat(suffix)
    );
  }
}
