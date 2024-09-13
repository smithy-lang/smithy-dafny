package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;

import java.util.HashMap;

public class ShapeVisitorHelper {
    public static final HashMap<Shape, Boolean> shapeOptionalityMap = new HashMap<>();
    
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
            if (!DafnyToSmithyShapeVisitor.visitorFuncMap.containsKey(targetShape)) {
                DafnyToSmithyShapeVisitor.visitorFuncMap.put(targetShape, "");
                DafnyToSmithyShapeVisitor.visitorFuncMap.put(
                    targetShape, 
                    targetShape.accept(
                        new DafnyToSmithyShapeVisitor(context, funcDataSource.concat(maybeAssertion), writer, isConfigShape, isOptional)
                    )
                );
            }
            nextVisitorFunction = (targetShape.getId().getName()).concat("_FromDafny(").concat(dataSource).concat(")");
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
            if (!SmithyToDafnyShapeVisitor.visitorFuncMap.containsKey(targetShape)) {
                shapeOptionalityMap.put(targetShape, isOptional);
                SmithyToDafnyShapeVisitor.visitorFuncMap.put(targetShape, "");
                SmithyToDafnyShapeVisitor.visitorFuncMap.put(
                    targetShape, 
                    targetShape.accept(
                        new SmithyToDafnyShapeVisitor(context, funcDataSource, writer, isConfigShape, isOptional, isPointerType)
                    )
                );
            }
            nextVisitorFunction = (targetShape.getId().getName()).concat("_ToDafny(").concat(dataSource).concat(")");
        }
        else {
            nextVisitorFunction = targetShape.accept(
                new SmithyToDafnyShapeVisitor(context, dataSource, writer, isConfigShape, isOptional, isPointerType)
            );
        }
        return nextVisitorFunction;
    }
}
