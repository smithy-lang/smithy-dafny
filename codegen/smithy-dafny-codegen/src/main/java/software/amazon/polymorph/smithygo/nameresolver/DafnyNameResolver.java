package software.amazon.polymorph.smithygo.nameresolver;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoSettings;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ToShapeId;

import static software.amazon.polymorph.smithygo.nameresolver.Constants.BLANK;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.DOT;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.INTERNAL_DAFNY;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.INTERNAL_DAFNY_TYPES;

public class DafnyNameResolver {

    public static String dafnyTypesNamespace(final Shape shape) {
        return shape.toShapeId().getNamespace()
                    .replace(DOT, BLANK).toLowerCase()
                    .concat(INTERNAL_DAFNY_TYPES);
    }

    public static String dafnyNamespace(final Shape shape) {
        return shape.toShapeId().getNamespace()
                    .replace(DOT, BLANK).toLowerCase()
                    .concat(INTERNAL_DAFNY);
    }

    public static String getDafnyType(final Shape shape, final Symbol symbol) {
        return DafnyNameResolver.dafnyTypesNamespace(shape)
                                .concat(DOT)
                                .concat(symbol.getName());
    }
    public static String getDafnySubErrorType(final Shape shape, final Symbol symbol) {
        return DafnyNameResolver.getDafnyBaseErrorType(shape)
                                .concat("_")
                                .concat(symbol.getName());
    }

    public static String getDafnyBaseErrorType(final Shape shape) {
        return DafnyNameResolver.dafnyTypesNamespace(shape)
                                .concat(DOT)
                                .concat("Error");
    }

    public static String getDafnyCompanionType(final Shape shape, final Symbol symbol) {
        return DafnyNameResolver.dafnyTypesNamespace(shape)
                                .concat(DOT)
                                .concat("Companion_%s_".formatted(symbol.getName()));
    }

    public static String getDafnyErrorCompanion(final Shape shape) {
        return DafnyNameResolver.dafnyTypesNamespace(shape)
                                .concat(DOT)
                                .concat("Companion_Error_");
    }

    public static String getDafnyErrorCompanionCreate(final Shape shape, final Symbol symbol) {
        return DafnyNameResolver.getDafnyErrorCompanion(shape)
                                .concat(DOT)
                                .concat("Create_%s_".formatted(symbol.getName()));
    }

    public static String getDafnyCompanionStructType(final Shape shape, final Symbol symbol) {
        return DafnyNameResolver.dafnyTypesNamespace(shape)
                                .concat(DOT)
                                .concat("CompanionStruct_%s_".formatted(symbol.getName()));
    }

    public static String getDafnyCompanionTypeCreate(final Shape shape, final Symbol symbol) {
        return DafnyNameResolver.getDafnyCompanionType(shape, symbol)
                                .concat(DOT)
                                .concat("Create_%s_".formatted(symbol.getName()));
    }

    public static String getDafnyClient(final Shape shape, final String sdkId) {
        return DafnyNameResolver.dafnyNamespace(shape)
                                .concat(DOT)
                                .concat(sdkId)
                                .concat("Client");
    }
    public static String getDafnyInterfaceClient(final Shape shape) {
        return DafnyNameResolver.dafnyTypesNamespace(shape)
                                .concat(DOT).concat("I")
                                .concat(shape.toShapeId().getName())
                                .concat("Client");
    }


    public static String createDafnyClient(final Shape shape, final String sdkId) {
        return DafnyNameResolver.dafnyNamespace(shape)
                                .concat(".Companion_Default___")
                                .concat(DOT)
                                .concat(sdkId);
    }

    public static String getDafnyDependentErrorType(final Shape shape, final String sdkId) {
        return DafnyNameResolver.dafnyNamespace(shape)
                                .concat(".Companion_Default___")
                                .concat(DOT)
                                .concat(sdkId);
    }

}
