package software.amazon.polymorph.smithygo.shapevisitor;

import java.util.Map.Entry;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SymbolUtils;
import software.amazon.polymorph.smithygo.codegen.knowledge.GoPointableIndex;
import software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.Symbol;
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
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.utils.CaseUtils;
import software.amazon.smithy.utils.StringUtils;

public class DafnyToSmithyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private final String dataSource;
    private final GoWriter writer;

    private final boolean isConfigShape;

    public DafnyToSmithyShapeVisitor(
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
        return "%s.Dtor_value().(%s)".formatted(dataSource, context.symbolProvider().toSymbol(shape));
    }

    @Override
    public String structureShape(final StructureShape shape) {
        final var builder = new StringBuilder();
        writer.addImport(DafnyNameResolver.dafnyTypesNamespace(context.settings()));
        builder.append("%1$s{".formatted("types.".concat(shape.getId().getName())));
        String fieldSeparator = "";
        for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
            builder.append(fieldSeparator);
            final var memberName = memberShapeEntry.getKey();
            final var memberShape = memberShapeEntry.getValue();
            final var targetShape = context.model().expectShape(memberShape.getTarget());

            if (targetShape.isStructureShape()) {
                final String[] refName = context.symbolProvider().toSymbol(memberShape).getFullName().split("/");
                 builder.append("%s: %s.Dtor_%s().Dtor_value().(*%s)".formatted(context.symbolProvider().toSymbol(memberShape).getName(), dataSource, memberName, refName[refName.length - 1]));
            } else {

                builder.append("%1$s: %2$s".formatted(
                        StringUtils.capitalize(memberName),
                        targetShape.accept(
                                new DafnyToSmithyShapeVisitor(context, dataSource + (memberShape.isOptional() ? ".Dtor_%s()".formatted(memberName) : ""), writer, isConfigShape)
                        )
                ));
            }
            fieldSeparator = ",";
        }

        return builder.append("}").toString();
    }

    // TODO: smithy-dafny-conversion library
    @Override
    public String listShape(ListShape shape) {
        final String[] refName = context.symbolProvider().toSymbol(shape).expectProperty(SymbolUtils.GO_ELEMENT_TYPE, Symbol.class).getFullName().split("/");
        return "%s.Dtor_value().([]%s)".formatted(dataSource, refName[refName.length - 1]);
    }

    @Override
    public String mapShape(MapShape shape) {
        final String[] refName = context.symbolProvider().toSymbol(shape).expectProperty(SymbolUtils.GO_ELEMENT_TYPE, Symbol.class).getFullName().split("/");
        return "%s.Dtor_value().(%s)".formatted(dataSource, "map[string]%s".formatted(refName[refName.length - 1]));
    }

    @Override
    public String booleanShape(BooleanShape shape) {
        return "&[]bool{%s.Dtor_value().(%s)}[0]".formatted(dataSource, context.symbolProvider().toSymbol(shape));
    }

    @Override
    public String stringShape(StringShape shape) {
        if (shape.hasTrait(EnumTrait.class)) {
            final String[] refName = context.symbolProvider().toSymbol(shape).getFullName().split("/");
            return "%s.(%s)".formatted(dataSource, refName[refName.length - 1]);
        }
        writer.addImport("dafny");
        return """
                func() (*string) {
                    var s string
                    for i := dafny.Iterate(%s.Dtor_value()) ; ; {
                        val, ok := i()
                        if !ok {
                            return &[]string{s}[0]
                        } else {
                            s = s + string(val.(dafny.Char))
                        }
                   }
               }(),
                """.formatted(dataSource);
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
        return getTypeAssertedShape(shape);
    }

    @Override
    public String longShape(LongShape shape) {
        return getTypeAssertedShape(shape);
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
        return getTypeAssertedShape(shape);
    }

    @Override
    public String bigDecimalShape(BigDecimalShape shape) {
        return getDefault(shape);
    }

    @Override
    public String enumShape(EnumShape shape) {
        return "%s.(%s)".formatted(dataSource, context.symbolProvider().toSymbol(shape).getNamespace());
    }

    @Override
    public String timestampShape(TimestampShape shape) {
        return getDefault(shape);
    }

    private String getTypeAssertedShape(final Shape shape) {
        return "%s.Dtor_value().(*%s)".formatted(dataSource, context.symbolProvider().toSymbol(shape));
    }
}
