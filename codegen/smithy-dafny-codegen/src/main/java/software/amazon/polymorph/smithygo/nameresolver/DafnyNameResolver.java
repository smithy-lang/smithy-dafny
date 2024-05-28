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

    public static String dafnyTypesNamespace(final ShapeId shapeId) {
        return shapeId.getNamespace().replace(DOT, BLANK).toLowerCase() + INTERNAL_DAFNY_TYPES;
    }

    public static String dafnyNamespace(final ShapeId shapeId) {
        return shapeId.getNamespace().replace(DOT, BLANK).toLowerCase() + INTERNAL_DAFNY;
    }

    public static String getDafnyType(final ShapeId shapeId, final Symbol symbol) {
        return DafnyNameResolver.dafnyTypesNamespace(shapeId).concat(DOT).concat(symbol.getName());
    }
    public static String getDafnySubErrorType(final ShapeId shapeId, final Symbol symbol) {
        return DafnyNameResolver.getDafnyBaseErrorType(shapeId).concat("_").concat(symbol.getName());
    }

    public static String getDafnyBaseErrorType(final ShapeId shapeId) {
        return DafnyNameResolver.dafnyTypesNamespace(shapeId).concat(DOT).concat("Error");
    }

    public static String getDafnyCompanionType(final ShapeId shapeId, final Symbol symbol) {
        return DafnyNameResolver.dafnyTypesNamespace(shapeId).concat(DOT).concat("Companion_%s_".formatted(symbol.getName()));
    }

    public static String getDafnyErrorCompanion(final ShapeId shapeId) {
        return DafnyNameResolver.dafnyTypesNamespace(shapeId).concat(DOT).concat("Companion_Error_");
    }

    public static String getDafnyErrorCompanionCreate(final ShapeId shapeId, final Symbol symbol) {
        return DafnyNameResolver.getDafnyErrorCompanion(shapeId).concat(DOT).concat("Create_%s_".formatted(symbol.getName()));
    }

    public static String getDafnyCompanionStructType(final ShapeId shapeId, final Symbol symbol) {
        return DafnyNameResolver.dafnyTypesNamespace(shapeId).concat(DOT).concat("CompanionStruct_%s_".formatted(symbol.getName()));
    }

    public static String getDafnyCompanionTypeCreate(final ShapeId shapeId, final Symbol symbol) {
        return DafnyNameResolver.getDafnyCompanionType(shapeId, symbol).concat(DOT).concat("Create_%s_".formatted(symbol.getName()));
    }

    public static String getDafnyClient(final ShapeId shapeId, final String sdkId) {
        return DafnyNameResolver.dafnyNamespace(shapeId).concat(DOT).concat(sdkId).concat("Client");
    }
    public static String getDafnyInterfaceClient(final ShapeId shapeId, final String sdkId) {
        return DafnyNameResolver.dafnyTypesNamespace(shapeId).concat(DOT).concat("I").concat(shapeId.getName()).concat("Client");
    }


    public static String createDafnyClient(final ShapeId shapeId, final String sdkId) {
        return DafnyNameResolver.dafnyNamespace(shapeId).concat(".Companion_Default___").concat(DOT).concat(sdkId);
    }

    public static String getDafnyDependentErrorType(final ShapeId shapeId, final String sdkId) {
        return DafnyNameResolver.dafnyNamespace(shapeId).concat(".Companion_Default___").concat(DOT).concat(sdkId);
    }

}
