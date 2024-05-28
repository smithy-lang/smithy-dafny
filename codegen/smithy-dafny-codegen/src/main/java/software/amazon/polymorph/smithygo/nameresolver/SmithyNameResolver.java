package software.amazon.polymorph.smithygo.nameresolver;

import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ToShapeId;

import static software.amazon.polymorph.smithygo.nameresolver.Constants.BLANK;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.DOT;

public class SmithyNameResolver {

    public static String shapeNamespace(final Shape shape) {
        return shape.toShapeId().getNamespace().replace(DOT, BLANK).toLowerCase();
    }

    public static String smithyTypesNamespace(final Shape shape) {
        return shape.toShapeId().getNamespace().replace(DOT, BLANK).toLowerCase().concat("types");
    }

    public static String smithyTypeConversionNamespace(final Shape shape) {
        return shape.toShapeId().getNamespace().replace(DOT, BLANK).toLowerCase().concat("typeconversion");
    }

    public static String getSmithyType(final Shape shape, final Symbol symbol) {
        return SmithyNameResolver.smithyTypesNamespace(shape).concat(DOT).concat(symbol.getName());
    }

    public static String getToDafnyMethodName(final ServiceShape serviceShape, final ToShapeId shapeId, final String disambiguator) {
        var methodName = serviceShape.getContextualName(shapeId);
        return methodName.concat(disambiguator).concat("_ToDafny");
    }

    public static String getFromDafnyMethodName(final ServiceShape serviceShape, final ToShapeId shapeId, final String disambiguator) {
        var methodName = serviceShape.getContextualName(shapeId);
        return methodName.concat(disambiguator).concat("_FromDafny");
    }

    public static String getInputToDafnyMethodName(final ServiceShape serviceShape, final ToShapeId shapeId) {
        return getToDafnyMethodName(serviceShape, shapeId, "_Input");
    }

    public static String getOutputToDafnyMethodName(final ServiceShape serviceShape, final ToShapeId shapeId) {
        return getToDafnyMethodName(serviceShape, shapeId, "_Output");
    }


    public static String getOutputFromDafnyMethodName(final ServiceShape serviceShape, final ToShapeId shapeId) {
        return getFromDafnyMethodName(serviceShape, shapeId, "_Output");
    }

    public static String getInputFromDafnyMethodName(final ServiceShape serviceShape, final ToShapeId shapeId) {
        return getFromDafnyMethodName(serviceShape, shapeId, "_Input");
    }

    public static String withNamespace(final Shape shape, final String shapeName) {
        return shapeNamespace(shape).concat(DOT).concat(shapeName);
    }
}
