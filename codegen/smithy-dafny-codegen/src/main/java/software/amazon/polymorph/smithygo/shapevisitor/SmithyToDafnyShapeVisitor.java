package software.amazon.polymorph.smithygo.shapevisitor;

import java.util.Map;
import java.util.Map.Entry;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.knowledge.GoPointableIndex;
import software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.BigDecimalShape;
import software.amazon.smithy.model.shapes.BigIntegerShape;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.ByteShape;
import software.amazon.smithy.model.shapes.DoubleShape;
import software.amazon.smithy.model.shapes.EnumShape;
import software.amazon.smithy.model.shapes.FloatShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.utils.CaseUtils;
import software.amazon.smithy.utils.StringUtils;

public class SmithyToDafnyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private final String dataSource;
    private final GoWriter writer;
    private final boolean isConfigShape;

    public SmithyToDafnyShapeVisitor(
            final GenerationContext context,
            final String dataSource,
            final GoWriter writer,
            final boolean isConfigShape
    ) {
        this.context = context;
        this.dataSource = dataSource;
        this.writer = writer;
        this.isConfigShape = isConfigShape;
    }

    @Override
    protected String getDefault(Shape shape) {
        throw new CodegenException(String.format(
                "Unsupported conversion of %s to %s using the %s protocol",
                shape, shape.getType(), context.protocolGenerator().getName()));
    }

    @Override
    public String blobShape(BlobShape shape) {
        writer.addImport("dafny");
        return """
                func () dafny.Sequence {
                    var v []interface{}
                    for _, e := range %s {
                    	v = append(v, e)
                    }
                    return dafny.SeqOf(v...);
                }(),
                """.formatted(dataSource);
    }

    @Override
    public String structureShape(final StructureShape shape) {
        final var builder = new StringBuilder();
        writer.addImport("Wrappers");
        writer.addImport(DafnyNameResolver.dafnyTypesNamespace(context.settings()));
        String companionStruct;
        if (shape.hasTrait(ErrorTrait.class)) {
            companionStruct = DafnyNameResolver.getDafnyErrorCompanionCreate(context.settings(), context.symbolProvider().toSymbol(shape));
        } else {
            companionStruct = DafnyNameResolver.getDafnyCompanionTypeCreate(context.settings(), context.symbolProvider().toSymbol(shape));
        }
        builder.append("%1$s(".formatted(companionStruct));
        String fieldSeparator = "";
        for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
            builder.append(fieldSeparator);
            final var memberName = memberShapeEntry.getKey();
            final var memberShape = memberShapeEntry.getValue();
            final var targetShape = context.model().expectShape(memberShape.getTarget());
            builder.append("%1$s%2$s%3$s".formatted(
                    memberShape.isOptional() ? "Wrappers.Companion_Option_.Create_Some_(" : "",
                    targetShape.accept(
                            new SmithyToDafnyShapeVisitor(context,                     GoPointableIndex.of(context.model()).isPointable(memberShape) && !targetShape.isStructureShape()?
                                                                                       "*%s".formatted(dataSource + "." + StringUtils.capitalize(memberName)) : dataSource + "." + StringUtils.capitalize(memberName),
                                                          writer, isConfigShape)),
                    memberShape.isOptional() ? ")" : ""
            ));
            fieldSeparator = ",";
        }


        return builder.append(")").toString();
    }

    @Override
    public String mapShape(MapShape shape) {
        StringBuilder builder = new StringBuilder();

        writer.addImport("dafny");

        MemberShape keyMemberShape = shape.getKey();
        final Shape keyTargetShape = context.model().expectShape(keyMemberShape.getTarget());
        MemberShape valueMemberShape = shape.getValue();
        final Shape valueTargetShape = context.model().expectShape(valueMemberShape.getTarget());

        builder.append("""
                func () dafny.Map {
		fieldValue := dafny.NewMapBuilder()
		for key, val := range %s {
			fieldValue.Add(%s, %s)
		}
		return fieldValue.ToMap()
	}(),""".formatted(dataSource,
                keyTargetShape.accept(
                        new SmithyToDafnyShapeVisitor(context, "key", writer, isConfigShape)
                )
        ,valueTargetShape.accept(
                        new SmithyToDafnyShapeVisitor(context, "val", writer, isConfigShape)
                )
        ));

        // Close structure
        return builder.toString();    }

    @Override
    public String listShape(ListShape shape) {
        writer.addImport("dafny");

        StringBuilder builder = new StringBuilder();

        MemberShape memberShape = shape.getMember();
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());

        builder.append("""
                func () dafny.Sequence {
		var fieldValue []interface{} = make([]interface{}, 0)
		for _, val := range %s {
			element := %s
			fieldValue = append(fieldValue, element)
		}
		return dafny.SeqOf(fieldValue...)
	}(),""".formatted(dataSource,
                targetShape.accept(
                        new SmithyToDafnyShapeVisitor(context, "val", writer, isConfigShape)
                )));

        // Close structure
        return builder.toString();    }

    @Override
    public String booleanShape(BooleanShape shape) {
        return dataSource;
    }

    @Override
    public String stringShape(StringShape shape) {
        writer.addImport("dafny");
        if (shape.hasTrait(EnumTrait.class)) {
            return """
        func () interface{} {
		var index int
		for _, enumVal := range %s.Values() {
			index++
			if enumVal == %s{
				break;
			}
		}
		var enum interface{}
		for allEnums, i := dafny.Iterate(%s{}.AllSingletonConstructors()), 0; i < index; i++ {
			var ok bool
			enum, ok = allEnums()
			if !ok {
				break;
			}
		}
		return enum
	}(),
                    """.formatted(dataSource, dataSource, DafnyNameResolver.getDafnyCompanionStructType(context.settings(), context.symbolProvider().toSymbol(shape)));
        } else {
            return "dafny.SeqOfChars([]dafny.Char(%s)...)".formatted(dataSource);
        }
    }

    @Override
    public String byteShape(ByteShape shape) {
        return getDefault(shape);
    }

    @Override
    public String shortShape(ShortShape shape) {
        return getDefault(shape);
    }

    @Override
    public String integerShape(IntegerShape shape) {
        return dataSource;
    }

    @Override
    public String longShape(LongShape shape) {
        return dataSource;
    }

    @Override
    public String bigIntegerShape(BigIntegerShape shape) {
        return getDefault(shape);
    }

    @Override
    public String floatShape(FloatShape shape) {
        return getDefault(shape);
    }

    @Override
    public String doubleShape(DoubleShape shape) {
        writer.addImport("dafny");
        writer.addImport("encoding/binary");
        writer.addImport("math");
        return """
                func () dafny.Sequence {
    	            var bits = math.Float64bits(%s)
                    var bytes = make([]byte, 8)
                    binary.LittleEndian.PutUint64(bytes, bits)
    	            var v []interface{}
    	            for _, e := range bytes {
    		            v = append(v, e)
    	            }
    	            return dafny.SeqOf(v...);
                }(),
	
    """.formatted(dataSource);
    }

    @Override
    public String bigDecimalShape(BigDecimalShape shape) {
        return getDefault(shape);
    }

    @Override
    public String enumShape(EnumShape shape) {
        return dataSource;
    }

    @Override
    public String timestampShape(TimestampShape shape) {
        return getDefault(shape);
    }
}
