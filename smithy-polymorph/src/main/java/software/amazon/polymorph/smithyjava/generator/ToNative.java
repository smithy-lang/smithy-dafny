package software.amazon.polymorph.smithyjava.generator;

import com.squareup.javapoet.ClassName;

import java.util.Map;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.smithy.model.shapes.ShapeType;

import static software.amazon.polymorph.smithyjava.generator.Generator.Constants.IDENTITY_FUNCTION;

public abstract class ToNative extends Generator {
    protected final static String VAR_INPUT = "dafnyValue";
    protected final static String VAR_OUTPUT = "converted";
    protected final static String VAR_TEMP = "temp";
    protected final static String TO_NATIVE = "ToNative";
    protected final static String NATIVE_BUILDER = "nativeBuilder";
    /**
     * The keys are the Dafny generated java input type,
     * the values are the method that converts from that input to the
     * idiomatic java type.
     */
    protected static final Map<ShapeType, MethodReference> AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    protected static final Map<ShapeType, MethodReference> SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    protected static final ClassName COMMON_TO_NATIVE_SIMPLE = ClassName.get(software.amazon.dafny.conversion.ToNative.Simple.class);
    protected static final ClassName COMMON_TO_NATIVE_AGGREGATE = ClassName.get(software.amazon.dafny.conversion.ToNative.Aggregate.class);

    static {
        AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.LIST, new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToList")),
                Map.entry(ShapeType.SET, new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToSet")),
                Map.entry(ShapeType.MAP, new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToMap"))
        );
        SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.BLOB, new MethodReference(COMMON_TO_NATIVE_SIMPLE, "ByteBuffer")),
                Map.entry(ShapeType.BOOLEAN, IDENTITY_FUNCTION),
                Map.entry(ShapeType.STRING, new MethodReference(COMMON_TO_NATIVE_SIMPLE, "String")),
                // TODO: Timestamp should be service specific
                Map.entry(ShapeType.TIMESTAMP, new MethodReference(COMMON_TO_NATIVE_SIMPLE, "Date")),
                Map.entry(ShapeType.BYTE, IDENTITY_FUNCTION),
                Map.entry(ShapeType.SHORT, IDENTITY_FUNCTION),
                Map.entry(ShapeType.INTEGER, IDENTITY_FUNCTION),
                Map.entry(ShapeType.LONG, IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_DECIMAL, IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_INTEGER, IDENTITY_FUNCTION)
        );
    }
    /**
     * The class name of the Subject's Shim's ToNative class.
     */
    protected final ClassName thisClassName;

    public ToNative(CodegenSubject subject, ClassName className) {
        super(subject);
        thisClassName = className;
    }
}
