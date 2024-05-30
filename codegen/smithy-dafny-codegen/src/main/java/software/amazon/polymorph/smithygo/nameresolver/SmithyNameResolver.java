package software.amazon.polymorph.smithygo.nameresolver;

import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;

import static software.amazon.polymorph.smithygo.nameresolver.Constants.BLANK;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.DOT;

public class SmithyNameResolver {

    public static String shapeNamespace(final Shape shape) {
        return shape.toShapeId().getNamespace().replace(DOT, BLANK).toLowerCase();
    }

    public static String smithyTypesNamespace(final Shape shape) {
        return shape.toShapeId().getNamespace().replace(DOT, BLANK).toLowerCase().concat("types");
    }

    public static String getSmithyType(final Shape shape, final Symbol symbol) {
        return SmithyNameResolver.smithyTypesNamespace(shape).concat(DOT).concat(symbol.getName());
    }

    public static String getToDafnyMethodName(final ServiceShape serviceShape, final Shape shape, final String disambiguator) {
        final var methodName = serviceShape.getContextualName(shape);
        return methodName.concat(disambiguator).concat("_ToDafny");
    }

    public static String getFromDafnyMethodName(final ServiceShape serviceShape, final Shape shape, final String disambiguator) {
        final var methodName = serviceShape.getContextualName(shape);
        return methodName.concat(disambiguator).concat("_FromDafny");
    }

    public static String getInputToDafnyMethodName(final ServiceShape serviceShape, final Shape shape) {
        final var methodName = getToDafnyMethodName(serviceShape, shape, "_Input");
        if (serviceShape.toShapeId().getNamespace().equals(shape.toShapeId().getNamespace())) {
            return methodName;
        }
        return smithyTypesNamespace(shape).concat(DOT).concat(methodName);
    }

    public static String getOutputToDafnyMethodName(final ServiceShape serviceShape, final Shape shape) {
        final var methodName = getToDafnyMethodName(serviceShape, shape, "_Output");
        if (serviceShape.toShapeId().getNamespace().equals(shape.toShapeId().getNamespace())) {
            return methodName;
        }
        return smithyTypesNamespace(shape).concat(DOT).concat(methodName);
    }


    public static String getOutputFromDafnyMethodName(final ServiceShape serviceShape, final Shape shape) {
        final var methodName =  getFromDafnyMethodName(serviceShape, shape, "_Output");
        if (serviceShape.toShapeId().getNamespace().equals(shape.toShapeId().getNamespace())) {
            return methodName;
        }
        return smithyTypesNamespace(shape).concat(DOT).concat(methodName);
    }

    public static String getInputFromDafnyMethodName(final ServiceShape serviceShape, final Shape shape) {
        final var methodName =  getFromDafnyMethodName(serviceShape, shape, "_Input");
        if (serviceShape.toShapeId().getNamespace().equals(shape.toShapeId().getNamespace())) {
            return methodName;
        }
        return smithyTypesNamespace(shape).concat(DOT).concat(methodName);
    }
}
