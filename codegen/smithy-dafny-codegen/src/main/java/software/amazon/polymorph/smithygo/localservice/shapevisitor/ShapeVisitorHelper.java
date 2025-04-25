package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import java.util.HashMap;
import java.util.Map;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithygo.utils.Constants;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;

/**
 * This class is a delegator / helper class for the ShapeVisitors to allow visitors generate the
 * typeconversion functions for acyclic shapes. In case of Recursive shapes, this class checks if the shape
 * has already been visited, and if yes then it re-uses the generated method instead of delegating
 * it again to the shape visitors. This helps in avoiding infinite recursion.
 */
public class ShapeVisitorHelper {

  private static final Map<MemberShape, Boolean> optionalShapesToDafny =
    new HashMap<>();

  public static boolean isToDafnyShapeOptional(final MemberShape shape) {
    return optionalShapesToDafny.get(shape);
  }

  /**
   * Generates the ToNative conversion function.
   * @param memberShape to operate on
   * @param context codegen context
   * @param dataSource the dafny variable name aka data source
   * @param assertionRequired if the shape is a generic type and needs typecasting / assertion.
   * @param writer used to write to the Go package.
   * @param isConfigShape if the shape is a local service config shape
   * @param isOptional if the shape is optional and might require unwrapping.
   * @return the generated type conversion function as a string
   */
  public static String toNativeShapeVisitorWriter(
    final MemberShape memberShape,
    final GenerationContext context,
    final String dataSource,
    final boolean assertionRequired,
    final GoWriter writer,
    final boolean isConfigShape,
    final boolean isOptional
  ) {
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());
    String maybeAssertion = "";
    if (assertionRequired) {
      final var refShape = targetShape.hasTrait(ReferenceTrait.class)
        ? targetShape.expectTrait(ReferenceTrait.class).getReferentId()
        : null;
      final String baseType = refShape == null
        ? DafnyNameResolver.getDafnyType(
          targetShape,
          context.symbolProvider().toSymbol(targetShape)
        )
        : DafnyNameResolver.getDafnyType(
          context.model().expectShape(refShape),
          context
            .symbolProvider()
            .toSymbol(memberShape)
            .getProperty("Referred", Symbol.class)
            .get()
        );
      maybeAssertion = ".(".concat(baseType).concat(")");
    }
    // Resource shape already goes into a function
    if (targetShape.hasTrait(ReferenceTrait.class)) {
      final ReferenceTrait referenceTrait = targetShape.expectTrait(
        ReferenceTrait.class
      );
      final Shape resourceOrService = context
        .model()
        .expectShape(referenceTrait.getReferentId());
      if (resourceOrService.isResourceShape()) {
        return targetShape.accept(
          new DafnyToSmithyShapeVisitor(
            context,
            dataSource.concat(maybeAssertion),
            writer,
            isConfigShape,
            isOptional
          )
        );
      }
    }
    final String funcName = Constants.funcNameGenerator(
      memberShape,
      "FromDafny"
    );
    final var serviceShape = context
      .model()
      .expectShape(context.settings().getService(), ServiceShape.class);
    // if the memberShape is an external shape, delegate to the type conversion in that namespace
    if (
      !serviceShape
        .getId()
        .getNamespace()
        .equals(memberShape.getId().getNamespace())
    ) {
      var memberShapeNameSpace = SmithyNameResolver.shapeNamespace(memberShape);
      return (
        memberShapeNameSpace
          .concat(".")
          .concat(funcName.concat("("))
          .concat(dataSource)
          .concat(")")
      );
    }
    final String funcDataSource = "input";
    if (
      !DafnyToSmithyShapeVisitor
        .getAllShapesRequiringConversionFunc()
        .contains(memberShape)
    ) {
      DafnyToSmithyShapeVisitor.putShapesWithConversionFunc(memberShape, "");
      DafnyToSmithyShapeVisitor.putShapesWithConversionFunc(
        memberShape,
        targetShape.accept(
          new DafnyToSmithyShapeVisitor(
            context,
            funcDataSource.concat(maybeAssertion),
            writer,
            isConfigShape,
            isOptional
          )
        )
      );
    }
    return (funcName.concat("(").concat(dataSource).concat(")"));
  }

  /**
   * Generates the ToDafny conversion function.
   * @param memberShape to operate on
   * @param context codegen context
   * @param dataSource the native variable name aka data source
   * @param writer used to write to the Go package.
   * @param isConfigShape if the shape is a local service config shape
   * @param isOptional if the shape is optional and might require wrapping.
   * @param isPointerType if the shape is a pointer type and might require dereferencing.
   * @return the generated type conversion function as a string
   */
  public static String toDafnyShapeVisitorWriter(
    final MemberShape memberShape,
    final GenerationContext context,
    final String dataSource,
    final GoWriter writer,
    final boolean isConfigShape,
    final boolean isOptional,
    final boolean isPointerType
  ) {
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());
    // Resource shape already goes into a function
    if (targetShape.hasTrait(ReferenceTrait.class)) {
      final ReferenceTrait referenceTrait = targetShape.expectTrait(
        ReferenceTrait.class
      );
      final Shape resourceOrService = context
        .model()
        .expectShape(referenceTrait.getReferentId());
      if (resourceOrService.isResourceShape()) {
        return targetShape.accept(
          new SmithyToDafnyShapeVisitor(
            context,
            dataSource,
            writer,
            isConfigShape,
            isOptional,
            isPointerType
          )
        );
      }
    }
    final String funcName = Constants.funcNameGenerator(memberShape, "ToDafny");
    final var serviceShape = context
      .model()
      .expectShape(context.settings().getService(), ServiceShape.class);
    if (
      !serviceShape
        .getId()
        .getNamespace()
        .equals(memberShape.getId().getNamespace())
    ) {
      var memberShapeNameSpace = SmithyNameResolver.shapeNamespace(memberShape);
      return (
        memberShapeNameSpace
          .concat(".")
          .concat(funcName.concat("("))
          .concat(dataSource)
          .concat(")")
      );
    }
    final String funcDataSource = "input";
    if (
      !SmithyToDafnyShapeVisitor
        .getAllShapesRequiringConversionFunc()
        .contains(memberShape)
    ) {
      optionalShapesToDafny.put(memberShape, isOptional);
      SmithyToDafnyShapeVisitor.putShapesWithConversionFunc(memberShape, "");
      SmithyToDafnyShapeVisitor.putShapesWithConversionFunc(
        memberShape,
        targetShape.accept(
          new SmithyToDafnyShapeVisitor(
            context,
            funcDataSource,
            writer,
            isConfigShape,
            isOptional,
            isPointerType
          )
        )
      );
    }
    return (funcName.concat("(").concat(dataSource).concat(")"));
  }
}
