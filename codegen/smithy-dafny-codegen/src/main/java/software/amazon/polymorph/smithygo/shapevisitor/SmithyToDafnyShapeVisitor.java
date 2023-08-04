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
import software.amazon.smithy.utils.CaseUtils;

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
                shape, shape.getType()));
    }

    @Override
    public String blobShape(BlobShape shape) {
        return dataSource;
    }

    @Override
    public String structureShape(final StructureShape shape) {
        final var builder = new StringBuilder();
        writer.addImport("Wrappers");
        writer.addImport(DafnyNameResolver.dafnyTypesNamespace(context.settings()));
        builder.append("%1$s(".formatted(DafnyNameResolver.getDafnyCompanionTypeCreate(context.settings(), context.symbolProvider().toSymbol(shape))));
        for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
            final var memberName = memberShapeEntry.getKey();
            final var memberShape = memberShapeEntry.getValue();
            final var targetShape = context.model().expectShape(memberShape.getTarget());
            builder.append("%1$s%2$s%3$s%4$s".formatted(
                    memberShape.isOptional() && !isConfigShape ? "Wrappers.Companion_Option_.Create_Some_(" : "",
                    GoPointableIndex.of(context.model()).isPointable(memberShape) ? "*" : "",
                    targetShape.accept(
                            new SmithyToDafnyShapeVisitor(context,
                                                          dataSource + "." + CaseUtils.toPascalCase(memberName),
                                                          writer, isConfigShape)),
                    memberShape.isOptional() && !isConfigShape ? ")" : ""
            ));
        }


        return builder.append(")").toString();
    }

    @Override
    public String mapShape(MapShape shape) {
        return getDefault(shape);
    }

    @Override
    public String listShape(ListShape shape) {
        return getDefault(shape);
    }

    @Override
    public String booleanShape(BooleanShape shape) {
        return dataSource;
    }

    @Override
    public String stringShape(StringShape shape) {
        return dataSource;
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
        return dataSource;
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
