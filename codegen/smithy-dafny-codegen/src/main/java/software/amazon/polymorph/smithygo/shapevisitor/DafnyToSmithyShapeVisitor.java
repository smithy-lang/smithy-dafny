package software.amazon.polymorph.smithygo.shapevisitor;

import java.util.Map.Entry;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.knowledge.GoPointableIndex;
import software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver;
import software.amazon.smithy.codegen.core.CodegenException;
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
                shape, shape.getType()));
    }

    @Override
    public String blobShape(BlobShape shape) {
        return getTypeAssertedShape(shape);
    }

    @Override
    public String structureShape(final StructureShape shape) {
        final var builder = new StringBuilder();
        writer.addImport(DafnyNameResolver.dafnyTypesNamespace(context.settings()));
        builder.append("%1$s{".formatted("types.".concat(shape.getId().getName())));
        for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
            final var memberName = memberShapeEntry.getKey();
            final var memberShape = memberShapeEntry.getValue();
            final var targetShape = context.model().expectShape(memberShape.getTarget());

            // Adds `smithy_structure_member=DafnyStructureMember(...)`
            // e.g.
            // smithy_structure_name(smithy_structure_member=DafnyStructureMember(...), ...)
            builder.append("%1$s".formatted(

                    targetShape.accept(
                            new DafnyToSmithyShapeVisitor(context, dataSource + (memberShape.isOptional() ? ".Dtor_value()" : ""), writer, isConfigShape)
                    )
            ));
        }

        return builder.append("}").toString();
    }

    // TODO: smithy-dafny-conversion library
    @Override
    public String listShape(ListShape shape) {
        return getDefault(shape);
    }

    @Override
    public String mapShape(MapShape shape) {
        return getDefault(shape);
    }

    @Override
    public String booleanShape(BooleanShape shape) {
        return "&[]bool{%s.(%s)}[0]".formatted(dataSource, context.symbolProvider().toSymbol(shape));
    }

    @Override
    public String stringShape(StringShape shape) {
        if (shape.hasTrait(EnumTrait.class)) {
            final String[] refName = context.symbolProvider().toSymbol(shape).getFullName().split("/");
            return "%s.(%s)".formatted(dataSource, refName[refName.length - 1]);
        }
        return getTypeAssertedShape(shape);
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
        return "%s.(*%s)".formatted(dataSource, context.symbolProvider().toSymbol(shape));
    }
}
