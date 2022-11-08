package software.amazon.polymorph.smithyjava.generator;

import com.squareup.javapoet.ClassName;

import java.util.Map;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.smithy.model.shapes.ShapeType;

public abstract class ToDafny extends Generator {
    /**
     * The keys are the input type, the values are the method that converts from that input to the Dafny type
     */
    protected static final Map<ShapeType, MethodReference> AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    protected static final Map<ShapeType, MethodReference> SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    protected static final ClassName COMMON_TO_DAFNY_SIMPLE = ClassName.get(software.amazon.dafny.conversion.ToDafny.Simple.class);
    protected static final ClassName COMMON_TO_DAFNY_AGGREGATE = ClassName.get(software.amazon.dafny.conversion.ToDafny.Aggregate.class);
    /**
     * The class name of the AWS SDK's Service's Shim's ToDafny class.
     */
    protected final ClassName thisClassName;

    public ToDafny(CodegenSubject subject) {
        super(subject);
        thisClassName = ClassName.get(subject.dafnyNameResolver.packageName(), "ToDafny");
    }

    static {
        AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.LIST, new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToSequence")),
                Map.entry(ShapeType.SET, new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToSet")),
                Map.entry(ShapeType.MAP, new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToMap"))
        );
        SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.BLOB, new MethodReference(COMMON_TO_DAFNY_SIMPLE, "ByteSequence")),
                Map.entry(ShapeType.BOOLEAN, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.STRING, new MethodReference(COMMON_TO_DAFNY_SIMPLE, "CharacterSequence")),
                Map.entry(ShapeType.TIMESTAMP, new MethodReference(COMMON_TO_DAFNY_SIMPLE, "CharacterSequence")),
                Map.entry(ShapeType.BYTE, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.SHORT, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.INTEGER, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.LONG, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_DECIMAL, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_INTEGER, Constants.IDENTITY_FUNCTION)
        );
    }
}
