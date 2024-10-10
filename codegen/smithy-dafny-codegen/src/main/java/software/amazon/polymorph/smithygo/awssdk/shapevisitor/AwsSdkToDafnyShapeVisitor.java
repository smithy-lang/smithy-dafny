package software.amazon.polymorph.smithygo.awssdk.shapevisitor;

import static software.amazon.polymorph.smithygo.localservice.nameresolver.Constants.DOT;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import software.amazon.polymorph.smithygo.awssdk.AwsSdkGoPointableIndex;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.DoubleShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.utils.StringUtils;

public class AwsSdkToDafnyShapeVisitor extends ShapeVisitor.Default<String> {

  private final GenerationContext context;
  private final String dataSource;
  private final GoWriter writer;
  private final boolean isConfigShape;

  private final boolean isOptional;
  protected boolean isPointerType;
  //TODO: Ideally this shouldn't be static but with current design we need to access this across instances.
  private static final Map<MemberShape, String> memberShapeConversionFuncMap = new HashMap<>();

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

  public static Set<MemberShape> getAllShapesRequiringConversionFunc() {
    return memberShapeConversionFuncMap.keySet();
  }

  public static void putShapesWithConversionFunc(final MemberShape shape, final String conversionFunc) {
    memberShapeConversionFuncMap.put(shape, conversionFunc);
  }

  public static String getConversionFunc(final MemberShape shape) {
    return memberShapeConversionFuncMap.get(shape);
  }

  @Override
  protected String getDefault(final Shape shape) {
    throw new CodegenException(
      String.format(
        "Unsupported conversion of %s to %s using the %s protocol",
        shape,
        shape.getType(),
        context.protocolGenerator().getName()
      )
    );
  }

  @Override
  public String blobShape(final BlobShape shape) {
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
    }()""".formatted(
        returnType,
        dataSource,
        nilWrapIfRequired,
        dataSource,
        someWrapIfRequired.formatted("dafny.SeqOf(v...)")
      );
  }

  @Override
  public String structureShape(final StructureShape shape) {
    final var builder = new StringBuilder();
    writer.addImportFromModule(
      "github.com/dafny-lang/DafnyStandardLibGo",
      "Wrappers"
    );
    writer.addImportFromModule(
      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
        shape.toShapeId().getNamespace()
      ),
      DafnyNameResolver.dafnyTypesNamespace(shape)
    );

    String someWrapIfRequired = "%s";

    final String companionStruct;
    String returnType;
    if (shape.hasTrait(ErrorTrait.class)) {
      companionStruct =
        DafnyNameResolver.getDafnyErrorCompanionCreate(
          shape,
          context.symbolProvider().toSymbol(shape)
        );
      returnType = DafnyNameResolver.getDafnyBaseErrorType(shape);
    } else {
      companionStruct =
        DafnyNameResolver.getDafnyCompanionTypeCreate(
          shape,
          context.symbolProvider().toSymbol(shape)
        );
      returnType =
        DafnyNameResolver.getDafnyType(
          shape,
          context.symbolProvider().toSymbol(shape)
        );
    }
    String nilWrapIfRequired = returnType.concat("{}");

    if (this.isOptional) {
      nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
      someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
      returnType = "Wrappers.Option";
    }

    var nilCheck = "";
    if (isPointerType) {
      nilCheck =
        "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
    }
    final var goCodeBlock =
      """
      func () %s {
          %s
          return %s
      }()""";

    builder.append("%1$s(".formatted(companionStruct));
    final String fieldSeparator = ",";
    for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
      final var memberName = memberShapeEntry.getKey();
      final var memberShape = memberShapeEntry.getValue();

      builder.append(
        "%1$s%2$s".formatted(
            ShapeVisitorHelper.toDafnyShapeVisitorWriter(
              memberShape,
              context,
              dataSource.concat(".").concat(StringUtils.capitalize(memberName)),
              writer,
              isConfigShape,
              memberShape.isOptional(),
              AwsSdkGoPointableIndex
                .of(context.model())
                .isPointable(memberShape)
            ),
            fieldSeparator
          )
      );
    }

    return goCodeBlock.formatted(
      returnType,
      nilCheck,
      someWrapIfRequired.formatted(builder.append(")").toString())
    );
  }

  @Override
  public String mapShape(final MapShape shape) {
    final StringBuilder builder = new StringBuilder();

    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");

    final var keyMemberShape = shape.getKey();
    final var valueMemberShape = shape.getValue();

    var nilWrapIfRequired = "nil";
    var someWrapIfRequired = "%s";
    var returnType = "dafny.Map";

    if (this.isOptional) {
      nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
      someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
      returnType = "Wrappers.Option";
    }
    var nilCheck = "";
    if (isPointerType) {
      nilCheck =
        "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
    }
    builder.append(
      """
      func () %s {
          %s
      	   fieldValue := dafny.NewMapBuilder()
      	   for key, val := range %s {
      		    fieldValue.Add(%s, %s)
      	   }
      	   return %s
      }()""".formatted(
          returnType,
          nilCheck,
          dataSource,
          ShapeVisitorHelper.toDafnyShapeVisitorWriter(
              keyMemberShape,
              context,
              "key",
              writer,
              isConfigShape,
              false,
              false
            ),
          ShapeVisitorHelper.toDafnyShapeVisitorWriter(
            valueMemberShape,
              context,
              "val",
              writer,
              isConfigShape,
              false,
              false
            ),
          someWrapIfRequired.formatted("fieldValue.ToMap()")
        )
    );

    // Close structure
    return builder.toString();
  }

  @Override
  public String listShape(final ListShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");

    final var builder = new StringBuilder();
    final var memberShape = shape.getMember();

    var nilWrapIfRequired = "nil";
    var someWrapIfRequired = "%s";
    var returnType = "dafny.Sequence";
    if (this.isOptional) {
      nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
      someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
      returnType = "Wrappers.Option";
    }

    builder.append(
      """
      func () %s {
             if %s == nil { return %s }
             var fieldValue []interface{} = make([]interface{}, 0)
             for _, val := range %s {
                 element := %s
                 fieldValue = append(fieldValue, element)
             }
             return %s
      }()""".formatted(
          returnType,
          dataSource,
          nilWrapIfRequired,
          dataSource,
          ShapeVisitorHelper.toDafnyShapeVisitorWriter(
            memberShape,
            context,
            "val",
            writer,
            isConfigShape,
            false,
            false
          ),
          someWrapIfRequired.formatted("dafny.SeqOf(fieldValue...)")
        )
    );

    // Close structure
    return builder.toString();
  }

  @Override
  public String booleanShape(final BooleanShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    String nilWrapIfRequired = "false";
    String someWrapIfRequired = "%s%s";
    String returnType = "bool";
    if (this.isOptional) {
      nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
      someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s%s)";
      returnType = "Wrappers.Option";
    }

    final var dereferenceIfRequired = isPointerType ? "*" : "";
    var nilCheck = "";
    if (isPointerType) {
      nilCheck =
        "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
    }

    return """
    func () %s {
        %s
        return %s
    }()""".formatted(
        returnType,
        nilCheck,
        someWrapIfRequired.formatted(dereferenceIfRequired, dataSource)
      );
  }

  @Override
  public String stringShape(final StringShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    if (shape.hasTrait(EnumTrait.class)) {
      String someWrapIfRequired = "%s";
      String returnType = DafnyNameResolver.getDafnyType(
        shape,
        context.symbolProvider().toSymbol(shape)
      );
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
      }()""".formatted(
          returnType,
          dataSource,
          dataSource,
          DafnyNameResolver.getDafnyCompanionStructType(
            shape,
            context.symbolProvider().toSymbol(shape)
          ),
          someWrapIfRequired.formatted(
            "enum.(%s)".formatted(
                DafnyNameResolver.getDafnyType(
                  shape,
                  context.symbolProvider().toSymbol(shape)
                )
              )
          )
        );
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
      final var dereferenceIfRequired = isPointerType ? "*" : "";
      if (isPointerType) {
        nilCheck =
          "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
      }

      if (shape.hasTrait(DafnyUtf8BytesTrait.class)) {
        writer.addUseImports(SmithyGoDependency.stdlib("unicode/utf8"));
      }
      final var underlyingType = shape.hasTrait(DafnyUtf8BytesTrait.class)
        ? """
            dafny.SeqOf(func () []interface{} {
            utf8.ValidString(%s%s)
            b := []byte(%s%s)
            f := make([]interface{}, len(b))
            for i, v := range b {
                f[i] = v
            }
            return f
        }()...)""".formatted(
            dereferenceIfRequired,
            dataSource,
            dereferenceIfRequired,
            dataSource
          )
        : "dafny.SeqOfChars([]dafny.Char(%s%s)...)".formatted(
            dereferenceIfRequired,
            dataSource
          );

      return """
      func () %s {
          %s
          return %s
      }()""".formatted(
          returnType,
          nilCheck,
          someWrapIfRequired.formatted(underlyingType)
        );
    }
  }

  @Override
  public String integerShape(final IntegerShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    String nilWrapIfRequired = "0";
    String someWrapIfRequired = "%s%s";
    String returnType = "int";
    if (this.isOptional) {
      nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
      someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s%s)";
      returnType = "Wrappers.Option";
    }

    final var dereferenceIfRequired = isPointerType ? "*" : "";
    var nilCheck = "";
    if (isPointerType) {
      nilCheck =
        "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
    }

    return """
    func () %s {
        %s
        return %s
    }()""".formatted(
        returnType,
        nilCheck,
        someWrapIfRequired.formatted(dereferenceIfRequired, dataSource)
      );
  }

  @Override
  public String longShape(final LongShape shape) {
    String nilWrapIfRequired = "0";
    String someWrapIfRequired = "%s%s";
    String returnType = "int64";
    if (this.isOptional) {
      nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
      someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s%s)";
      returnType = "Wrappers.Option";
    }

    final var dereferenceIfRequired = isPointerType ? "*" : "";
    var nilCheck = "";
    if (isPointerType) {
      nilCheck =
        "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
    }

    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");

    return """
    func () %s {
        %s
        return %s
    }()""".formatted(
        returnType,
        nilCheck,
        someWrapIfRequired.formatted(dereferenceIfRequired, dataSource)
      );
  }

  @Override
  public String doubleShape(final DoubleShape shape) {
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

    final var dereferenceIfRequired = isPointerType ? "*" : "";
    var nilCheck = "";
    if (isPointerType) {
      nilCheck =
        "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
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
    }()""".formatted(
        returnType,
        nilCheck,
        dereferenceIfRequired,
        dataSource,
        someWrapIfRequired.formatted("dafny.SeqOf(v...)")
      );
  }

  @Override
  public String unionShape(final UnionShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");

    final var serviceShape = context
      .model()
      .expectShape(context.settings().getService(context.model()).toShapeId())
      .asServiceShape().get();

    final var internalDafnyType = DafnyNameResolver.getDafnyType(
      shape,
      context.symbolProvider().toSymbol(shape)
    );

    var returnType = DafnyNameResolver.getDafnyType(shape, context.symbolProvider().toSymbol(shape));
    var someWrapIfRequired = "%s(%s)";
    if (this.isOptional) {
      returnType = "Wrappers.Option";
      someWrapIfRequired =
        "Wrappers.Companion_Option_.Create_Some_(%s(%s))";
    }

    final var functionInit =
      """
        func() %s {
            switch %s.(type) {""".formatted(returnType, dataSource);

    final var eachMemberInUnion = new StringBuilder();
    for (final var member : shape.getAllMembers().values()) {
      final var memberName = context.symbolProvider().toMemberName(member);
      final var targetShape = context.model().expectShape(member.getTarget());
      final var baseType = DafnyNameResolver.getDafnyType(targetShape, context.symbolProvider().toSymbol(targetShape));
      final var dataSourceInput = dataSource
        .concat(".(*")
        .concat(SmithyNameResolver.smithyTypesNamespaceAws(serviceShape.expectTrait(ServiceTrait.class), true))
        .concat(DOT)
        .concat(context.symbolProvider().toMemberName(member))
        .concat(").Value");
      eachMemberInUnion.append(
        """
          case *%s.%s:
              var companion = %s
              var inputToConversion = %s
              return %s
          """.formatted(
          SmithyNameResolver.smithyTypesNamespaceAws(serviceShape.expectTrait(ServiceTrait.class), true),
          context.symbolProvider().toMemberName(member),
          internalDafnyType.replace(
            shape.getId().getName(),
            "CompanionStruct_".concat(shape.getId().getName()).concat("_{}")
          ),
          ShapeVisitorHelper.toDafnyShapeVisitorWriter(
            member,
            context,
            dataSourceInput,
            writer,
            isConfigShape,
            true,
            false
          ),
          someWrapIfRequired.formatted(
            DafnyNameResolver.getDafnyCreateFuncForUnionMemberShape(
              shape,
              memberName
            ),
            "inputToConversion.UnwrapOr(nil)%s".formatted(
              !baseType.isEmpty() ? ".(".concat(baseType).concat(")") : ""
            )
          )
        )
      );
    }

    final var defaultCase =
      """
                default:
        panic("Unhandled union type")
            }
        }()""";
    return """
      %s
      %s
      %s""".formatted(functionInit, eachMemberInUnion, defaultCase);
  }

  @Override
  public String timestampShape(final TimestampShape shape) {
    //TODO: This is a stub implementation and not working yet.
    writer.addImport("time");
    if (this.isOptional) {
      return "Wrappers.Companion_Option_.Create_None_()";
    }
    return "dafny.SeqOf()";
  }
}
