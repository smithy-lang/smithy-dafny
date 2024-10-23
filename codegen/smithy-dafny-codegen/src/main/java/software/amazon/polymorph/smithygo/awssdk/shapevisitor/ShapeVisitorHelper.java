package software.amazon.polymorph.smithygo.awssdk.shapevisitor;

import java.util.HashMap;
import java.util.Map;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.utils.Constants;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.EnumTrait;

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
    if (targetShape.hasTrait(ReferenceTrait.class)) {
      return targetShape.accept(
        new AwsSdkToDafnyShapeVisitor(
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
            isConfigShape,
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
