package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.knowledge.GoPointableIndex;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;

import java.util.HashMap;

public class ShapeVisitorHelper {
    public static final HashMap<MemberShape, Boolean> toDafnyOptionalityMap = new HashMap<>();

    /**
     * Generates functions Name for To Dafny and To Native conversion.
     *
     * @param memberShape       MemberShape to generate function name for.
     * @param suffix            Suffix to add to the function. As of this writing, we only put FromDafny or ToNative suffix.
     * @return the function Name
     */
    public static String funcNameGenerator(final MemberShape memberShape, final String suffix) {
        return memberShape
            .getId()
            .toString()
            .replaceAll("[.$#]","_")
            .concat("_")
            .concat(suffix);
    }
    
    public static String toNativeContainerShapeHelper (final MemberShape memberShape, final GenerationContext context, final String dataSource, final Boolean assertionRequired, final GoWriter writer, final boolean isConfigShape, final boolean isOptional) {
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());
        String maybeAssertion = "";
        if (assertionRequired) {
            maybeAssertion = ".("
                .concat(DafnyNameResolver.getDafnyType(targetShape, context.symbolProvider().toSymbol(targetShape)))
                .concat(")");
        }
        String nextVisitorFunction;
        if (!targetShape.hasTrait(ReferenceTrait.class) && (targetShape.isStructureShape() || targetShape.isUnionShape() || targetShape.isListShape() || targetShape.isMapShape())) {
            String funcDataSource = "input";
            if (!DafnyToSmithyShapeVisitor.visitorFuncMap.containsKey(memberShape)) {
                DafnyToSmithyShapeVisitor.visitorFuncMap.put(memberShape, "");
                DafnyToSmithyShapeVisitor.visitorFuncMap.put(
                    memberShape, 
                    targetShape.accept(
                        new DafnyToSmithyShapeVisitor(context, funcDataSource.concat(maybeAssertion), writer, isConfigShape, isOptional)
                    )
                );
            }
            String funcName = funcNameGenerator(memberShape, "FromDafny");
            nextVisitorFunction = funcName.concat("(").concat(dataSource).concat(")");
        } else {
            nextVisitorFunction = targetShape.accept(
                new DafnyToSmithyShapeVisitor(context, dataSource.concat(maybeAssertion), writer, isConfigShape, isOptional)
            );
        }
        return nextVisitorFunction;
    }

    public static String toDafnyContainerShapeHelper (final MemberShape memberShape, final GenerationContext context, final String dataSource, final GoWriter writer, final boolean isConfigShape, final boolean isOptional, final boolean isPointerType) {
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());
        String nextVisitorFunction;
        if (!targetShape.hasTrait(ReferenceTrait.class) && (targetShape.isStructureShape() || targetShape.isUnionShape() || targetShape.isMapShape() || targetShape.isListShape())) {
            String funcDataSource = "input";
            if (!SmithyToDafnyShapeVisitor.visitorFuncMap.containsKey(memberShape)) {
                toDafnyOptionalityMap.put(memberShape, isOptional);
                SmithyToDafnyShapeVisitor.visitorFuncMap.put(memberShape, "");
                SmithyToDafnyShapeVisitor.visitorFuncMap.put(
                    memberShape, 
                    targetShape.accept(
                        new SmithyToDafnyShapeVisitor(context, funcDataSource, writer, isConfigShape, isOptional, isPointerType)
                    )
                );
            }
            String funcName = (memberShape.getId().toString().replaceAll("[.$#]","_")).concat("_ToDafny(");
            nextVisitorFunction = funcName.concat(dataSource).concat(")");
        }
        else {
            nextVisitorFunction = targetShape.accept(
                new SmithyToDafnyShapeVisitor(context, dataSource, writer, isConfigShape, isOptional, isPointerType)
            );
        }
        return nextVisitorFunction;
    }
}
