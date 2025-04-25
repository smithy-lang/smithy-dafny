package software.amazon.polymorph.smithygo.awssdk.shapevisitor;

import java.util.HashMap;
import java.util.Map;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.utils.Constants;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.EnumTrait;

/**
 * This class is a delegator / helper class for the ShapeVisitors to allow visitors generate the
 * typeconversion functions for acyclic shapes. In case of Recursive shapes, this class checks if the shape
 * has already been visited, and if yes then it re-uses the generated method instead of delegating
 * it again to the shape visitors. This helps in avoiding infinite recursion, and has aws-sdk specific logic.
 */
public class ShapeVisitorHelper {

  private static final Map<MemberShape, Boolean> optionalShapesToDafny =
    new HashMap<>();
  private static final Map<MemberShape, Boolean> pointerShapesToNative =
    new HashMap<>();

  public static boolean isToDafnyShapeOptional(final MemberShape shape) {
    return optionalShapesToDafny.get(shape);
  }

  public static boolean isToNativeShapePointable(final MemberShape shape) {
    return pointerShapesToNative.get(shape);
  }

  /**
   * Generates the ToNative conversion function.
   * @param memberShape to operate on
   * @param context codegen context
   * @param dataSource the dafny variable name aka data source
   * @param assertionRequired if the shape is a generic type and needs typecasting / assertion.
   * @param writer used to write to the Go package.
   * @param isOptional if the shape is optional and might require unwrapping.
   * @param isPointable if the shape is a pointer and might require referencing/dereferencing.
   * @return the generated type conversion function as a string
   */
  public static String toNativeShapeVisitorWriter(
    final MemberShape memberShape,
    final GenerationContext context,
    final String dataSource,
    final boolean assertionRequired,
    final GoWriter writer,
    final boolean isOptional,
    final boolean isPointable
  ) {
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());
    String maybeAssertion = "";
    if (assertionRequired && !targetShape.hasTrait(EnumTrait.class)) {
      maybeAssertion =
        ".(".concat(
            DafnyNameResolver.getDafnyType(
              targetShape,
              context.symbolProvider().toSymbol(targetShape)
            )
          )
          .concat(")");
    }
    final String funcDataSource = "input";
    if (
      !DafnyToAwsSdkShapeVisitor
        .getAllShapesRequiringConversionFunc()
        .contains(memberShape)
    ) {
      DafnyToAwsSdkShapeVisitor.putShapesWithConversionFunc(memberShape, "");
      DafnyToAwsSdkShapeVisitor.putShapesWithConversionFunc(
        memberShape,
        targetShape.accept(
          new DafnyToAwsSdkShapeVisitor(
            context,
            funcDataSource.concat(maybeAssertion),
            writer,
            isOptional,
            isPointable
          )
        )
      );
      pointerShapesToNative.put(memberShape, isPointable);
    }
    final String funcName = Constants.funcNameGenerator(
      memberShape,
      "FromDafny"
    );
    return (funcName.concat("(").concat(dataSource).concat(")"));
  }

  /**
   * Generates the ToDafny conversion function.
   * @param memberShape to operate on
   * @param context codegen context
   * @param dataSource the native variable name aka data source
   * @param writer used to write to the Go package.
   * @param isOptional if the shape is optional and might require wrapping.
   * @param isPointerType if the shape is a pointer type and might require dereferencing.
   * @return the generated type conversion function as a string
   */
  public static String toDafnyShapeVisitorWriter(
    final MemberShape memberShape,
    final GenerationContext context,
    final String dataSource,
    final GoWriter writer,
    final boolean isOptional,
    final boolean isPointerType
  ) {
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());
    final String funcDataSource = "input";
    if (
      !AwsSdkToDafnyShapeVisitor
        .getAllShapesRequiringConversionFunc()
        .contains(memberShape)
    ) {
      optionalShapesToDafny.put(memberShape, isOptional);
      AwsSdkToDafnyShapeVisitor.putShapesWithConversionFunc(memberShape, "");
      AwsSdkToDafnyShapeVisitor.putShapesWithConversionFunc(
        memberShape,
        targetShape.accept(
          new AwsSdkToDafnyShapeVisitor(
            context,
            funcDataSource,
            writer,
            isOptional,
            isPointerType
          )
        )
      );
    }
    final String funcName = Constants.funcNameGenerator(memberShape, "ToDafny");
    return (funcName.concat("(").concat(dataSource).concat(")"));
  }
}
