package software.amazon.polymorph.smithygo.awssdk.shapevisitor;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.awssdk.AwsSdkGoPointableIndex;
import software.amazon.polymorph.smithygo.codegen.SymbolUtils;
import software.amazon.polymorph.smithygo.codegen.knowledge.GoPointableIndex;
import software.amazon.polymorph.smithygo.localservice.DafnyGoPointableIndex;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithygo.utils.GoCodegenUtils;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.DoubleShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.utils.StringUtils;

import java.util.Arrays;
import java.util.List;

public class DafnyToAwsSdkShapeVisitor extends ShapeVisitor.Default<String> {
    private static final List<String> shapeName = Arrays.asList("IndexSizeBytes", "ItemCount", "ProcessedSizeBytes", "TableSizeBytes");
    private final AwsSdkGoPointableIndex awsSdkGoPointableIndex;
    private final GenerationContext context;
    private final String dataSource;
    private final GoWriter writer;
    private final ServiceTrait serviceTrait;
    private final boolean isOptional;
    private final boolean isPointable;

    public DafnyToAwsSdkShapeVisitor(
            final GenerationContext context,
            final String dataSource,
            final GoWriter writer
    ) {
        this(context, dataSource, writer, false, false);
    }

    public DafnyToAwsSdkShapeVisitor(
            final GenerationContext context,
            final String dataSource,
            final GoWriter writer,
            final boolean isOptional,
            final boolean isPointable
    ) {
        this.context = context;
        this.dataSource = dataSource;
        this.writer = writer;
        this.isOptional = isOptional;
        this.isPointable = isPointable;
        this.awsSdkGoPointableIndex = new AwsSdkGoPointableIndex(context.model());
        this.serviceTrait = context.model().expectShape(context.settings().getService(context.model()).toShapeId()).getTrait(ServiceTrait.class).get();
    }

    @Override
    protected String getDefault(Shape shape) {
        throw new CodegenException(String.format(
                "Unsupported conversion of %s to %s using the %s protocol",
                shape, shape.getType(), context.protocolGenerator().getName()));
    }

    @Override
    public String blobShape(BlobShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
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
        final var builder = new StringBuilder();
        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(shape.toShapeId().getNamespace()), DafnyNameResolver.dafnyTypesNamespace(shape));
        var subtype = !(shape.toShapeId().getName().contains("Input") || shape.toShapeId().getName().contains("Output"))
                              || shape.toShapeId().getName().contains("Exception");
        var nilcheck = "";
        if (this.isOptional) {
            if (this.isPointable) {
                nilcheck = "if %s == nil { return nil }".formatted(dataSource);
            } else {
                nilcheck = "";
            }
        }
        builder.append("""
                               func() %s%s {
                               %s
                               return %s%s {
                               """.formatted(this.isPointable ? "*" : "", SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, subtype).concat(".").concat(shape.getId().getName()),
                                             nilcheck,
                                             this.isPointable ? "&" : "",
                                             SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, subtype).concat(".").concat(shape.getId().getName()))
        );
        for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
            final var memberName = memberShapeEntry.getKey();
            final var memberShape = memberShapeEntry.getValue();
            final var targetShape = context.model().expectShape(memberShape.getTarget());
            //TODO: Is it ever possible for structure to be nil?
            final var derivedDataSource = "%1$s%2$s%3$s%4$s".formatted(dataSource, this.isOptional ? ".(%s)".formatted(DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape))) : "",
                                                                       ".Dtor_%s()".formatted(memberName),
                                                                       memberShape.isOptional() ? ".UnwrapOr(nil)" : "");
            builder.append("%1$s: %2$s,".formatted(
                    StringUtils.capitalize(memberName),
                    targetShape.accept(
                            new DafnyToAwsSdkShapeVisitor(context, derivedDataSource, writer, memberShape.isOptional(), shapeName.contains(memberName) || awsSdkGoPointableIndex.isPointable(memberShape))
                    )
            ));
        }

        return builder.append("}}()").toString();
    }

    // TODO: smithy-dafny-conversion library
    @Override
    public String listShape(ListShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        StringBuilder builder = new StringBuilder();

        MemberShape memberShape = shape.getMember();
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());
        var typeName = GoCodegenUtils.getType(context.symbolProvider().toSymbol(targetShape), serviceTrait);
        builder.append("""
                               func() []%s{
                                   var fieldValue []%s
                                   %s
                                   for i := dafny.Iterate(%s.(dafny.Sequence)); ; {
                                    val, ok := i()
                                    if !ok {
                                        break
                                    }
                                    fieldValue = append(fieldValue, %s)}
                               """.formatted(typeName, typeName, this.isOptional ? """
                                                     if %s == nil {
                                                         return nil
                                                     }""".formatted(dataSource) : "", dataSource,
                                             targetShape.accept(
                                                     new DafnyToAwsSdkShapeVisitor(context, "val%s".formatted(memberShape.isOptional() ? ".(%s)".formatted(DafnyNameResolver.getDafnyType(targetShape, context.symbolProvider().toSymbol(targetShape))) : ""), writer, false, awsSdkGoPointableIndex.isPointable(memberShape))
                                             )));

        // Close structure
        return builder.append("return fieldValue }()").toString();
    }

    @Override
    public String mapShape(MapShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        StringBuilder builder = new StringBuilder();

        MemberShape keyMemberShape = shape.getKey();
        final Shape keyTargetShape = context.model().expectShape(keyMemberShape.getTarget());
        MemberShape valueMemberShape = shape.getValue();
        final Shape valueTargetShape = context.model().expectShape(valueMemberShape.getTarget());
        var typeName = GoCodegenUtils.getType(context.symbolProvider().toSymbol(valueTargetShape), serviceTrait);

        var nilCheck = "";
        if (this.isOptional) {
            nilCheck = """
                    if %s == nil {
                        return nil
                    }
                    """.formatted(dataSource);
        }
        builder.append("""
                               func() map[string]%s {
                                   var m map[string]%s = make(map[string]%s)
                                   %s
                                   for i := dafny.Iterate(%s%s.Items());; {
                                       val, ok := i()
                                    	  if !ok {
                                    	      break;
                                    	  }
                                    	  m[%s] = %s
                                   }
                                   return m
                               }()""".formatted(typeName, typeName, typeName, nilCheck, dataSource, this.isOptional ? ".(dafny.Map)" : "",
                                                keyTargetShape.accept(
                                                        new DafnyToAwsSdkShapeVisitor(context, "(*val.(dafny.Tuple).IndexInt(0))", writer, keyMemberShape.isOptional(), awsSdkGoPointableIndex.isPointable(keyMemberShape))),
                                                valueTargetShape.accept(
                                                        new DafnyToAwsSdkShapeVisitor(context, "(*val.(dafny.Tuple).IndexInt(1))%s".formatted(valueMemberShape.isOptional() ? ".(%s)".formatted(DafnyNameResolver.getDafnyType(valueTargetShape, context.symbolProvider().toSymbol(valueTargetShape))) : ""), writer, false, awsSdkGoPointableIndex.isPointable(valueMemberShape))
                                                )
        ));
        return builder.toString();
    }

    @Override
    public String booleanShape(BooleanShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        var nilCheck = "";
        if (this.isOptional) {
            if (this.isPointable) {
                nilCheck = "if %s == nil { return nil }".formatted(dataSource);
            } else {
                nilCheck = "if %s == nil { return b }".formatted(dataSource);
            }
        }
        return """
                func() %sbool {
                    var b bool
                    %s
                    b = %s%s
                    return %sb
                }()""".formatted(this.isPointable ? "*" : "", nilCheck, dataSource, this.isOptional ? ".(%s)".formatted(context.symbolProvider().toSymbol(shape).getName()) : "",
                                 this.isPointable ? "&" : "");
    }

    @Override
    public String stringShape(StringShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        if (shape.hasTrait(EnumTrait.class)) {
            if (this.isOptional) {
                return """
                           func () %s.%s {
                           var u %s.%s
                            //TODO: What to do if nil
                            if %s == nil {
                                return u
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
                        	return u.Values()[index]
                        }()""".formatted(SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, true), context.symbolProvider().toSymbol(shape).getName(),
                                         SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, true), context.symbolProvider().toSymbol(shape).getName(),
                                         dataSource,
                                         dataSource, DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape)),
                                         DafnyNameResolver.getDafnyCompanionStructType(shape, context.symbolProvider().toSymbol(shape)),
                                         DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape)));
            } else {
                return """
                           func () %s.%s {
                           var u %s.%s
                        
                        	inputEnum := %s
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
                        	return u.Values()[index]
                        }()""".formatted(SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, true), context.symbolProvider().toSymbol(shape).getName(),
                                         SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, true), context.symbolProvider().toSymbol(shape).getName(),
                                         dataSource,
                                         DafnyNameResolver.getDafnyCompanionStructType(shape, context.symbolProvider().toSymbol(shape)),
                                         DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape)));
            }
        }

        var underlyingType = shape.hasTrait(DafnyUtf8BytesTrait.class) ? "uint8" : "dafny.Char";
        var nilCheck = "";
        if (this.isOptional) {
            if (this.isPointable) {
                nilCheck = "if %s == nil { return nil }".formatted(dataSource);
            } else {
                nilCheck = "if %s == nil { return s }".formatted(dataSource);
            }
        }
        return """
                 func() (%sstring) {
                     var s string
                 %s
                     for i := dafny.Iterate(%s) ; ; {
                         val, ok := i()
                         if !ok {
                             return %s[]string{s}[0]
                         } else {
                             s = s + string(val.(%s))
                         }
                    }
                }()""".formatted(this.isPointable ? "*" : "", nilCheck, dataSource, this.isPointable ? "&" : "", underlyingType);
    }

    @Override
    public String integerShape(IntegerShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        if (AwsSdkGoPointableIndex.of(context.model()).isPointable(shape)) {
            return """
                    func() *int32 {
                        var i int32
                        if %s == nil {
                            return nil
                        }
                        i = %s.(int32)
                        return &i
                    }()""".formatted(dataSource, dataSource);
        } else {
            return "%s.(%s)".formatted(dataSource, context.symbolProvider().toSymbol(shape).getName());
        }
    }

    @Override
    public String longShape(LongShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        var nilCheck = "";
        if (this.isOptional) {
            if (this.isPointable) {
                nilCheck = "if %s == nil { return nil }".formatted(dataSource);
            } else {
                nilCheck = "if %s == nil { return i}".formatted(dataSource);
            }
        }
        return """
                func() %sint64 {
                    var i int64
                    %s
                    i = %s%s
                    return %si
                }()""".formatted(this.isPointable ? "*" : "", nilCheck, dataSource, this.isOptional ? ".(int64)" : "", this.isPointable ? "&" : "");
    }

    @Override
    public String doubleShape(DoubleShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        writer.addUseImports(SmithyGoDependency.MATH);
        writer.addUseImports(SmithyGoDependency.stdlib("encoding/binary"));
        var nilCheck = "";
        if (this.isOptional) {
            if (this.isPointable) {
                nilCheck = "if %s == nil { return nil }".formatted(dataSource);
            } else {
                nilCheck = "if %s == nil { var f float64; return f}".formatted(dataSource);
            }
        }
        return """
                func () %sfloat64 {
                    var b []byte
                %s
                    for i := dafny.Iterate(%s) ; ; {
                        val, ok := i()
                	    if !ok {
                      return %s[]float64{math.Float64frombits(binary.LittleEndian.Uint64(b))}[0]
                     } else {
                      b = append(b, val.(byte))
                     }
                    }
                }()""".formatted(this.isPointable ? "*" : "", nilCheck, dataSource, this.isPointable ? "&" : "");
    }

    @Override
    public String unionShape(UnionShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        return """
                func () types.%s {
                _ = val
                return nil
                }()""".formatted(context.symbolProvider().toSymbol(shape).getName());
    }

    @Override
    public String timestampShape(TimestampShape shape) {
        return "nil";
    }

}
