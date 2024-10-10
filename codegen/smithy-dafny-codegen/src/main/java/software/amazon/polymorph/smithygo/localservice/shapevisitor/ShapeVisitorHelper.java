package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import java.util.HashMap;
import java.util.Map;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;

public class ShapeVisitorHelper {

  public static final Map<MemberShape, Boolean> toDafnyOptionalityMap =
    new HashMap<>();

  /**
   * Generates functions Name for To Dafny and To Native conversion.
   *
   * @param memberShape       MemberShape to generate function name for.
   * @param suffix            Suffix to add to the function. As of this writing, we only put FromDafny or ToNative suffix.
   * @return the function Name
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

  public static String toNativeShapeVisitorWriter(
    final MemberShape memberShape,
    final GenerationContext context,
    final String dataSource,
    final Boolean assertionRequired,
    final GoWriter writer,
    final boolean isConfigShape,
    final boolean isOptional
  ) {
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());
    String maybeAssertion = "";
    if (assertionRequired) {
      maybeAssertion =
        ".(".concat(
            DafnyNameResolver.getDafnyType(
              targetShape,
              context.symbolProvider().toSymbol(targetShape)
            )
          )
          .concat(")");
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
    final String nextVisitorFunction;
    final String funcDataSource = "input";
    if (!DafnyToSmithyShapeVisitor.VISITOR_FUNCTION_MAP.containsKey(memberShape)) {
      DafnyToSmithyShapeVisitor.VISITOR_FUNCTION_MAP.put(memberShape, "");
      DafnyToSmithyShapeVisitor.VISITOR_FUNCTION_MAP.put(
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
    final String funcName = funcNameGenerator(memberShape, "FromDafny");
    nextVisitorFunction = funcName.concat("(").concat(dataSource).concat(")");
    return nextVisitorFunction;
  }

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
    final String nextVisitorFunction;
    if (targetShape.hasTrait(ReferenceTrait.class)) {
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
    final String funcDataSource = "input";
    if (!SmithyToDafnyShapeVisitor.VISITOR_FUNCTION_MAP.containsKey(memberShape)) {
      toDafnyOptionalityMap.put(memberShape, isOptional);
      SmithyToDafnyShapeVisitor.VISITOR_FUNCTION_MAP.put(memberShape, "");
      SmithyToDafnyShapeVisitor.VISITOR_FUNCTION_MAP.put(
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
    final String funcName =
      (memberShape.getId().toString().replaceAll("[.$#]", "_")).concat(
          "_ToDafny("
        );
    nextVisitorFunction = funcName.concat(dataSource).concat(")");
    return nextVisitorFunction;
  }
}
