package software.amazon.polymorph.smithygo.awssdk.shapevisitor;

import java.util.HashMap;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.EnumTrait;

public class ShapeVisitorHelper {

  public static final HashMap<MemberShape, Boolean> toDafnyOptionalityMap =
    new HashMap<>();
  public static final HashMap<MemberShape, Boolean> toNativeOutputPointerMap =
    new HashMap<>();
  public static final HashMap<MemberShape, String> toNativeNextFuncInput =
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
    final boolean isOptional,
    final boolean isPointable
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
      if (targetShape.hasTrait(EnumTrait.class)) {
        maybeAssertion = "";
      }
    }
    String nextVisitorFunction;
    String funcDataSource = "input";
    if (!DafnyToAwsSdkShapeVisitor.visitorFuncMap.containsKey(memberShape)) {
      DafnyToAwsSdkShapeVisitor.visitorFuncMap.put(memberShape, "");
      DafnyToAwsSdkShapeVisitor.visitorFuncMap.put(
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
      toNativeOutputPointerMap.put(memberShape, isPointable);
    }
    String funcName = funcNameGenerator(memberShape, "FromDafny");
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
    String nextVisitorFunction;
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
    String funcDataSource = "input";
    if (!AwsSdkToDafnyShapeVisitor.visitorFuncMap.containsKey(memberShape)) {
      if (targetShape.isUnionShape())
        toDafnyOptionalityMap.put(memberShape, true);
      else
        toDafnyOptionalityMap.put(memberShape, isOptional);
      AwsSdkToDafnyShapeVisitor.visitorFuncMap.put(memberShape, "");
      AwsSdkToDafnyShapeVisitor.visitorFuncMap.put(
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
    String funcName =
      (memberShape.getId().toString().replaceAll("[.$#]", "_")).concat(
          "_ToDafny("
        );
    nextVisitorFunction = funcName.concat(dataSource).concat(")");
    return nextVisitorFunction;
  }
}
