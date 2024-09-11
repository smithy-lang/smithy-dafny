package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;

public class ShapeVisitorHelper {
    public static String toNativeContainerShapeHelper (final MemberShape memberShape, final GenerationContext context, final String dataSource, final Boolean assertionRequired, final GoWriter writer, final boolean isConfigShape, final boolean isOptional) {
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());
        String maybeAssertion = "";
        if (assertionRequired) {
            maybeAssertion = ".("
                .concat(DafnyNameResolver.getDafnyType(targetShape, context.symbolProvider().toSymbol(targetShape)))
                .concat(")");
        }
        String nextVisitorFunction = targetShape.accept(
                new DafnyToSmithyShapeVisitor(context, dataSource.concat(maybeAssertion), writer, isConfigShape, isOptional)
            );
        if (targetShape.isStructureShape() || targetShape.isUnionShape() || targetShape.isListShape() || targetShape.isMapShape()) {
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
        }
        return nextVisitorFunction;
    }

    // public static String toDafnyContainerShapeHelper (final MemberShape memberShape, final GenerationContext context, final String dataSource, final Boolean assertionRequired, final GoWriter writer, final boolean isConfigShape) {
    //     final Shape targetShape = context.model().expectShape(memberShape.getTarget());
    //     // String maybeAssertion = "";
    //     // if (assertionRequired) {
    //     //     maybeAssertion = ".("
    //     //         .concat(DafnyNameResolver.getDafnyType(targetShape, context.symbolProvider().toSymbol(targetShape)))
    //     //         .concat(")");
    //     // }
    //     String nextVisitorFunction = targetShape.accept(
    //             new DafnyToSmithyShapeVisitor(context, dataSource.concat(maybeAssertion), writer, isConfigShape, memberShape.isOptional())
    //         );
    //     if (targetShape.isStructureShape() || targetShape.isUnionShape() || targetShape.isListShape() || targetShape.isMapShape()) {
    //         String funcDataSource = "input";
    //         if (!DafnyToSmithyShapeVisitor.visitorFuncMap.containsKey(targetShape)) {
    //             DafnyToSmithyShapeVisitor.visitorFuncMap.put(targetShape, "");
    //             DafnyToSmithyShapeVisitor.visitorFuncMap.put(
    //                 targetShape, 
    //                 targetShape.accept(
    //                     new DafnyToSmithyShapeVisitor(context, funcDataSource.concat(maybeAssertion), writer, isConfigShape, memberShape.isOptional())
    //                 )
    //             );
    //         }
    //         nextVisitorFunction = (targetShape.getId().getName()).concat("_FromDafny(").concat(dataSource).concat(")");
    //     }
    //     return nextVisitorFunction;
    // }
}
