package software.amazon.polymorph.smithygo.shapevisitor;

import java.util.Map.Entry;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SymbolUtils;
import software.amazon.polymorph.smithygo.codegen.knowledge.GoPointableIndex;
import software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
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
import software.amazon.smithy.model.shapes.ShapeId;
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
    private final boolean isMemberShape;

    public DafnyToSmithyShapeVisitor(
            final GenerationContext context,
            final String dataSource,
            final GoWriter writer,
            final boolean isConfigShape
    ) {
        this(context, dataSource, writer, isConfigShape, false);
    }

    public DafnyToSmithyShapeVisitor(
            final GenerationContext context,
            final String dataSource,
            final GoWriter writer,
            final boolean isConfigShape,
            final boolean isMemberShape
    ) {
        this.context = context;
        this.dataSource = dataSource;
        this.writer = writer;
        this.isConfigShape = isConfigShape;
        this.isMemberShape = isMemberShape;
    }

    protected String referenceStructureShape(StructureShape shape) {
        ReferenceTrait referenceTrait = shape.expectTrait(ReferenceTrait.class);
        Shape resourceOrService = context.model().expectShape(referenceTrait.getReferentId());
        return "%1$s{%2$s}".formatted(resourceOrService.toShapeId().getName(), dataSource);
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
                func () []byte {
                var b []byte
                if %s == nil {
                    return nil
                }
                for i := dafny.Iterate(%s) ; ; {
                    val, ok := i()
                    if !ok {
                        return b
                    } else {
                        b = append(b, val.(byte))
                    }
                }
                }()""".formatted(dataSource, dataSource);
    }

    @Override
    public String structureShape(final StructureShape shape) {
        if (shape.hasTrait(ReferenceTrait.class)) {
            return referenceStructureShape(shape);
        }
        final var builder = new StringBuilder();
        writer.addImport(DafnyNameResolver.dafnyTypesNamespace(context.settings()));

        builder.append("%1$s{".formatted("types.".concat(shape.getId().getName())));
        String fieldSeparator = ",";
        for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
            final var memberName = memberShapeEntry.getKey();
            final var memberShape = memberShapeEntry.getValue();
            final var targetShape = context.model().expectShape(memberShape.getTarget());
            final var derivedDataSource = "%1$s%2$s%3$s%4$s".formatted(dataSource,
                                                                       isMemberShape ? ".(%s)".formatted(DafnyNameResolver.getDafnyType(context.settings(), context.symbolProvider().toSymbol(shape))) : "",
                                                                       ".Dtor_%s()".formatted(memberName),
                                                                       (memberShape.isOptional() ? ".UnwrapOr(nil)" : ""));
                builder.append("%1$s: %2$s%3$s,".formatted(
                        StringUtils.capitalize(memberName),
                        targetShape.isStructureShape() ? "&" : "",
                        targetShape.accept(
                                new DafnyToSmithyShapeVisitor(context, derivedDataSource, writer, isConfigShape, true)
                        )
                ));
        }

        return builder.append("}").toString();
    }

    // TODO: smithy-dafny-conversion library
    @Override
    public String listShape(ListShape shape) {
        StringBuilder builder = new StringBuilder();

        MemberShape memberShape = shape.getMember();
        final String[] typeName = context.symbolProvider().toSymbol(memberShape).getFullName().split("/");
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());
        builder.append("""
                       func() []%s{
                       var fieldValue []%s
                if %s == nil {
                    return nil
                }
		for i := dafny.Iterate(%s.(dafny.Sequence)); ; {
			val, ok := i()
			if !ok {
				break
			}
			fieldValue = append(fieldValue, %s%s)}
			""".formatted(typeName[typeName.length - 1], typeName[typeName.length - 1], dataSource, dataSource,
                targetShape.isStructureShape() ? "" : "*",
                targetShape.accept(
                        new DafnyToSmithyShapeVisitor(context, "val", writer, isConfigShape, true)
                )));

        // Close structure
        return builder.append("return fieldValue }()".formatted(dataSource)).toString();
    }

    @Override
    public String mapShape(MapShape shape) {
        StringBuilder builder = new StringBuilder();

        MemberShape keyMemberShape = shape.getKey();
        final Shape keyTargetShape = context.model().expectShape(keyMemberShape.getTarget());
        MemberShape valueMemberShape = shape.getValue();
        final Shape valueTargetShape = context.model().expectShape(valueMemberShape.getTarget());
        final var type = context.symbolProvider().toSymbol(valueTargetShape).getName();
        builder.append("""
                               func() map[string]%s {
                               var m map[string]%s = make(map[string]%s)
                if %s == nil {
                    return nil
                }
	for i := dafny.Iterate(%s.(dafny.Map).Items());; {
		val, ok := i()
		if !ok {
			break;
		}
		m[*%s] = *%s
	}
	return m
                               }()""".formatted(type, type, type, dataSource, dataSource, keyTargetShape.accept(
                new DafnyToSmithyShapeVisitor(context, "(*val.(dafny.Tuple).IndexInt(0))", writer, isConfigShape)
        ),
                valueTargetShape.accept(
                        new DafnyToSmithyShapeVisitor(context, "(*val.(dafny.Tuple).IndexInt(1))", writer, isConfigShape)
                )
        ));
        return builder.toString();
    }

    @Override
    public String booleanShape(BooleanShape shape) {
        return """
                func() *bool {
                    var b bool
                    if %s == nil {
                        return nil
                    }
                    b = %s.(%s)
                    return &b
                }()""".formatted(dataSource, dataSource, context.symbolProvider().toSymbol(shape));
    }

    @Override
    public String stringShape(StringShape shape) {
        writer.addImport("dafny");
        if (shape.hasTrait(EnumTrait.class)) {
            return """
    func () *types.%s {
    var u types.%s
                if %s == nil {
                    return nil
                }
		inputEnum := %s.(%s)
		index := -1;
		for allEnums := dafny.Iterate(%s{}.AllSingletonConstructors()); ; {
			enum, ok := allEnums()
			if ok {
				index++
				if enum.(%s).Equals(inputEnum) {
					break;
				}
			}
		}
		
		return &u.Values()[index]
	}()""".formatted(context.symbolProvider().toSymbol(shape).getName(), context.symbolProvider().toSymbol(shape).getName(), dataSource, dataSource, DafnyNameResolver.getDafnyType(context.settings(), context.symbolProvider().toSymbol(shape)), DafnyNameResolver.getDafnyCompanionStructType(context.settings(), context.symbolProvider().toSymbol(shape)),
                  DafnyNameResolver.getDafnyType(context.settings(), context.symbolProvider().toSymbol(shape)));
        }
        return """
                func() (*string) {
                    var s string
                if %s == nil {
                    return nil
                }
                    for i := dafny.Iterate(%s) ; ; {
                        val, ok := i()
                        if !ok {
                            return &[]string{s}[0]
                        } else {
                            s = s + string(val.(dafny.Char))
                        }
                   }
               }()""".formatted(dataSource, dataSource);
    }

    @Override
    public String integerShape(IntegerShape shape) {
        return ("""
                func() *int32 {
                    var b int32
                    if %s == nil {
                        return nil
                    }
                    b = %s.(int32)
                    return &b
                }()""").formatted(dataSource, dataSource);
    }

    @Override
    public String longShape(LongShape shape) {
        return ("""
                func() *int64 {
                    var b int64
                    if %s == nil {
                        return nil
                    }
                    b = %s.(int64)
                    return &b
                }()""").formatted(dataSource, dataSource);
    }

    @Override
    public String doubleShape(DoubleShape shape) {
        writer.addImport("dafny");
        writer.addImport("math");
        return """
                func () *float64 {
                    var b []byte
                if %s == nil {
                    return nil
                }
                    for i := dafny.Iterate(%s) ; ; {
                        val, ok := i()
                	    if !ok {
    		                return &[]float64{math.Float64frombits(binary.LittleEndian.Uint64(b))}[0]
    	                } else {
    		                b = append(b, val.(byte))
    	                }
                    }
                }()""".formatted(dataSource, dataSource);
    }
}
