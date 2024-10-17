package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import java.util.HashMap;
import java.util.Map;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;

import static software.amazon.polymorph.smithygo.utils.Constants.funcNameGenerator;

public class ShapeVisitorHelper {

  private static final Map<MemberShape, Boolean> optionalShapesToDafny =
    new HashMap<>();

  public static boolean isToDafnyShapeOptional(final MemberShape shape) {
    return optionalShapesToDafny.get(shape);
  }

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
    if (!DafnyToSmithyShapeVisitor.getAllShapesRequiringConversionFunc().contains(memberShape)) {
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
    if (!SmithyToDafnyShapeVisitor.getAllShapesRequiringConversionFunc().contains(memberShape)) {
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
    final String funcName = funcNameGenerator(memberShape, "ToDafny");
    nextVisitorFunction = funcName.concat("(").concat(dataSource).concat(")");
    return nextVisitorFunction;
  }
}
