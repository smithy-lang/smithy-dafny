package software.amazon.polymorph.smithygo.awssdk.shapevisitor;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.smithy.codegen.core.CodegenException;
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
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.utils.StringUtils;

import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;

public class AwsSdkToDafnyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private final String dataSource;
    private final GoWriter writer;
    private final boolean isConfigShape;

    private final boolean isOptional;
    protected boolean isPointerType;

    public void setPointerType() {
        this.isPointerType = false;
    }

    public AwsSdkToDafnyShapeVisitor(
            final GenerationContext context,
            final String dataSource,
            final GoWriter writer,
            final boolean isConfigShape,
            final boolean isOptional,
            final boolean isPointerType
    ) {
        this.context = context;
        this.dataSource = dataSource;
        this.writer = writer;
        this.isConfigShape = isConfigShape;
        this.isOptional = isOptional;
        this.isPointerType = isPointerType;
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
        String nilWrapIfRequired = "nil";
        String someWrapIfRequired = "%s";
        String returnType = "dafny.Sequence";
        if (this.isOptional) {
            nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
            someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
            returnType = "Wrappers.Option";
        }
        return """
                func () %s {
                    var v []interface{}
                    if %s == nil {return %s}
                    for _, e := range %s {
                    	v = append(v, e)
                    }
                    return %s;
                }()""".formatted(returnType, dataSource, nilWrapIfRequired, dataSource, someWrapIfRequired.formatted("dafny.SeqOf(v...)"));
    }

    @Override
    public String structureShape(final StructureShape shape) {
        final var builder = new StringBuilder();
        writer.addImportFromModule("github.com/dafny-lang/DafnyStandardLibGo", "Wrappers");
        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(shape.toShapeId().getNamespace()), DafnyNameResolver.dafnyTypesNamespace(shape));

        String someWrapIfRequired = "%s";

        String companionStruct;
        String returnType;
        if (shape.hasTrait(ErrorTrait.class)) {
            companionStruct = DafnyNameResolver.getDafnyErrorCompanionCreate(shape, context.symbolProvider().toSymbol(shape));
            returnType = DafnyNameResolver.getDafnyBaseErrorType(shape);
        } else {
            companionStruct = DafnyNameResolver.getDafnyCompanionTypeCreate(shape, context.symbolProvider().toSymbol(shape));
            returnType = DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape));
        }
        String nilWrapIfRequired = returnType.concat("{}");

        if (this.isOptional) {
            nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
            someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
            returnType = "Wrappers.Option";
        }

        var nilCheck = "";
        if (isPointerType) {
            nilCheck = "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
        }
        var goCodeBlock = """
                func () %s {
                    %s
                    return %s
                }()""";


        builder.append("%1$s(".formatted(companionStruct));
        String fieldSeparator = ",";
        for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
            final var memberName = memberShapeEntry.getKey();
            final var memberShape = memberShapeEntry.getValue();
            final var targetShape = context.model().expectShape(memberShape.getTarget());
            builder.append("%1$s%2$s".formatted(
                    targetShape.accept(
                            new AwsSdkToDafnyShapeVisitor(context, dataSource + "." + StringUtils.capitalize(memberName),
                                                                                                                       writer, isConfigShape, memberShape.isOptional(), context.symbolProvider().toSymbol(memberShape).getProperty(POINTABLE, Boolean.class).orElse(false)
                            )), fieldSeparator
            ));
        }


        return goCodeBlock.formatted(returnType, nilCheck, someWrapIfRequired.formatted(builder.append(")").toString()));
    }

    @Override
    public String mapShape(MapShape shape) {
        StringBuilder builder = new StringBuilder();

        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");

        MemberShape keyMemberShape = shape.getKey();
        final Shape keyTargetShape = context.model().expectShape(keyMemberShape.getTarget());
        MemberShape valueMemberShape = shape.getValue();
        final Shape valueTargetShape = context.model().expectShape(valueMemberShape.getTarget());
        String nilWrapIfRequired = "nil";
        String someWrapIfRequired = "%s";
        String returnType = "dafny.Map";
        if (this.isOptional) {
            nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
            someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
            returnType = "Wrappers.Option";
        }
        var nilCheck = "";
        if (isPointerType) {
            nilCheck = "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
        }
        builder.append("""
                               func () %s {
                                   %s
                               	   fieldValue := dafny.NewMapBuilder()
                               	   for key, val := range %s {
                               		    fieldValue.Add(%s, %s)
                               	   }
                               	   return %s
                               }()""".formatted(returnType, nilCheck, dataSource,
                                                keyTargetShape.accept(
                                                        new AwsSdkToDafnyShapeVisitor(context, "key", writer, isConfigShape, false, false)),
                                                valueTargetShape.accept(
                                                        new AwsSdkToDafnyShapeVisitor(context, "val", writer, isConfigShape, false, false)),
                                                someWrapIfRequired.formatted("fieldValue.ToMap()")
                       )
        );

        // Close structure
        return builder.toString();

    }

    @Override
    public String listShape(ListShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");

        StringBuilder builder = new StringBuilder();

        MemberShape memberShape = shape.getMember();
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());

        String nilWrapIfRequired = "nil";
        String someWrapIfRequired = "%s";
        String returnType = "dafny.Sequence";
        if (this.isOptional) {
            nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
            someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
            returnType = "Wrappers.Option";
        }

        builder.append("""
                               func () %s {
                                      if %s == nil { return %s }
                                      var fieldValue []interface{} = make([]interface{}, 0)
                                      for _, val := range %s {
                                          element := %s
                                          fieldValue = append(fieldValue, element)
                                      }
                                      return %s
                               }()""".formatted(returnType, dataSource, nilWrapIfRequired, dataSource,
                                                targetShape.accept(
                                                        new AwsSdkToDafnyShapeVisitor(context, "val", writer, isConfigShape, false, false)
                                                ), someWrapIfRequired.formatted("dafny.SeqOf(fieldValue...)")));

        // Close structure
        return builder.toString();
    }

    @Override
    public String booleanShape(BooleanShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        String nilWrapIfRequired = "false";
        String someWrapIfRequired = "%s%s";
        String returnType = "bool";
        if (this.isOptional) {
            nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
            someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s%s)";
            returnType = "Wrappers.Option";
        }

        var dereferenceIfRequired = isPointerType ? "*" : "";
        var nilCheck = "";
        if (isPointerType) {
            nilCheck = "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
        }

        return """
                func () %s {
                    %s
                    return %s
                }()""".formatted(returnType, nilCheck, someWrapIfRequired.formatted(dereferenceIfRequired, dataSource));
    }

    @Override
    public String stringShape(StringShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        if (shape.hasTrait(EnumTrait.class)) {
            String someWrapIfRequired = "%s";
            String returnType = DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape));
            if (this.isOptional) {
                someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
                returnType = "Wrappers.Option";
            }

            return """
                           func () %s {
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
                    	return %s
                    }()""".formatted(returnType, dataSource, dataSource, DafnyNameResolver.getDafnyCompanionStructType(shape, context.symbolProvider().toSymbol(shape)), someWrapIfRequired.formatted("enum.(%s)".formatted(DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape)))));
        } else {
            String nilWrapIfRequired = "nil";
            String someWrapIfRequired = "%s";
            String returnType = "dafny.Sequence";
            if (this.isOptional) {
                nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
                someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
                returnType = "Wrappers.Option";
            }

            var nilCheck = "";
            var dereferenceIfRequired = isPointerType ? "*" : "";
            if (isPointerType) {
                nilCheck = "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
            }

            if (shape.hasTrait(DafnyUtf8BytesTrait.class))
                writer.addUseImports(SmithyGoDependency.stdlib("unicode/utf8"));

            var underlyingType = shape.hasTrait(DafnyUtf8BytesTrait.class) ? """
                        dafny.SeqOf(func () []interface{} {
                        utf8.ValidString(%s%s)
                        b := []byte(%s%s)
                        f := make([]interface{}, len(b))
                        for i, v := range b {
                            f[i] = v
                        }
                        return f
                    }()...)""".formatted(dereferenceIfRequired, dataSource, dereferenceIfRequired, dataSource) : "dafny.SeqOfChars([]dafny.Char(%s%s)...)".formatted(dereferenceIfRequired, dataSource);

            return """
                    func () %s {
                        %s
                        return %s
                    }()""".formatted(returnType, nilCheck, someWrapIfRequired.formatted(underlyingType));
        }
    }

    @Override
    public String integerShape(IntegerShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        String nilWrapIfRequired = "0";
        String someWrapIfRequired = "%s%s";
        String returnType = "int";
        if (this.isOptional) {
            nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
            someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s%s)";
            returnType = "Wrappers.Option";
        }

        var dereferenceIfRequired = isPointerType ? "*" : "";
        var nilCheck = "";
        if (isPointerType) {
            nilCheck = "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
        }

        return """
                func () %s {
                    %s
                    return %s
                }()""".formatted(returnType, nilCheck, someWrapIfRequired.formatted(dereferenceIfRequired, dataSource));

    }

    @Override
    public String longShape(LongShape shape) {
        String nilWrapIfRequired = "0";
        String someWrapIfRequired = "%s%s";
        String returnType = "int64";
        if (this.isOptional) {
            nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
            someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s%s)";
            returnType = "Wrappers.Option";
        }

        var dereferenceIfRequired = isPointerType ? "*" : "";
        var nilCheck = "";
        if (isPointerType) {
            nilCheck = "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
        }

        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");

        return """
                func () %s {
                    %s
                    return %s
                }()""".formatted(returnType, nilCheck, someWrapIfRequired.formatted(dereferenceIfRequired, dataSource));
    }

    @Override
    public String doubleShape(DoubleShape shape) {
        writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
        writer.addUseImports(SmithyGoDependency.stdlib("encoding/binary"));
        writer.addUseImports(SmithyGoDependency.MATH);

        String nilWrapIfRequired = "dafny.SeqOf()";
        String someWrapIfRequired = "%s";
        String returnType = "dafny.Sequence";
        if (this.isOptional) {
            nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
            someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
            returnType = "Wrappers.Option";
        }

        var dereferenceIfRequired = isPointerType ? "*" : "";
        var nilCheck = "";
        if (isPointerType) {
            nilCheck = "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
        }

        return """
                func () %s {
                    %s
                 var bits = math.Float64bits(%s%s)
                    var bytes = make([]byte, 8)
                    binary.LittleEndian.PutUint64(bytes, bits)
                 var v []interface{}
                 for _, e := range bytes {
                  v = append(v, e)
                 }
                 return %s;
                }()""".formatted(returnType, nilCheck, dereferenceIfRequired, dataSource, someWrapIfRequired.formatted("dafny.SeqOf(v...)"));
    }

    @Override
    public String unionShape(UnionShape shape) {
        return """
                func () Wrappers.Option {
                _ = val
                return Wrappers.Companion_Option_.Create_None_()
                }()""";
    }

    @Override
    public String timestampShape(TimestampShape shape) {
        if (this.isOptional) {
            return "Wrappers.Companion_Option_.Create_None_()";
        }
        return "dafny.SeqOf()";
    }
}