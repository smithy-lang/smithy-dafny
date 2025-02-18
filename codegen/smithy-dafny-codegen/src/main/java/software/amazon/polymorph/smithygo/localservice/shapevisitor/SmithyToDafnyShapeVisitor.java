package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;
import static software.amazon.polymorph.smithygo.utils.Constants.DAFNY_RUNTIME_GO_LIBRARY_MODULE;
import static software.amazon.polymorph.smithygo.utils.Constants.SMITHY_DAFNY_STD_LIB_GO;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.DoubleShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.utils.StringUtils;

/**
 * This class is used to generate the type conversion method for native shapes to dafny shapes.
 * It uses the ShapeVisitor pattern to traverse the Smithy shapes and generate the corresponding Go type conversion code.
 */
// TODO: Remove anonymous function in each of the shape visitor and test if it will work
public class SmithyToDafnyShapeVisitor extends ShapeVisitor.Default<String> {

  private final GenerationContext context;
  private final String dataSource;
  private final GoWriter writer;
  private final boolean isConfigShape;

  private final boolean isOptional;
  protected boolean isPointerType;
  //TODO: Ideally this shouldn't be static but with current design we need to access this across instances.
  private static final Map<MemberShape, String> memberShapeConversionFuncMap =
    new LinkedHashMap<>();

  public SmithyToDafnyShapeVisitor(
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

  /**
   * Returns a set of all shapes that has been visited and has type conversion method generated.
   *
   * @return Set of MemberShape objects.
   */
  public static Set<MemberShape> getAllShapesRequiringConversionFunc() {
    return memberShapeConversionFuncMap.keySet();
  }

  /**
   * Puts the shape and its corresponding conversion function in the memberShapeConversionFuncMap.
   *
   * @param shape          MemberShape object.
   * @param conversionFunc String representing the conversion function.
   */
  public static void putShapesWithConversionFunc(
    final MemberShape shape,
    final String conversionFunc
  ) {
    memberShapeConversionFuncMap.put(shape, conversionFunc);
  }

  /**
   * Returns the conversion function for the given shape.
   *
   * @param shape MemberShape object.
   * @return String representing the conversion function.
   */
  public static String getConversionFunc(final MemberShape shape) {
    return memberShapeConversionFuncMap.get(shape);
  }

  /**
   * Return the conversion function for shapes with @reference trait.
   *
   * @param shape MemberShape object.
   * @return String representing the conversion function.
   */
  protected String referenceStructureShape(final StructureShape shape) {
    final ReferenceTrait referenceTrait = shape.expectTrait(
      ReferenceTrait.class
    );
    final Shape resourceOrService = context
      .model()
      .expectShape(referenceTrait.getReferentId());

    //Handle @reference{Resource} shape
    if (resourceOrService.asResourceShape().isPresent()) {
      final ResourceShape resourceShape = resourceOrService
        .asResourceShape()
        .get();
      var namespace = "";
      if (
        !resourceShape
          .toShapeId()
          .getNamespace()
          .equals(context.settings().getService().getNamespace())
      ) {
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            resourceShape.toShapeId().getNamespace()
          ),
          SmithyNameResolver.shapeNamespace(resourceShape)
        );
        namespace =
          SmithyNameResolver.shapeNamespace(resourceShape).concat(".");
      }
      if (!this.isOptional) {
        return "%s_ToDafny(%s)".formatted(
            namespace.concat(resourceShape.toShapeId().getName()),
            dataSource
          );
      } else {
        final var goCodeBlock =
          """
          func () Wrappers.Option {
              if (%s) == nil {
              return Wrappers.Companion_Option_.Create_None_()
              }
              return Wrappers.Companion_Option_.Create_Some_(%s)
          }()""";
        return goCodeBlock.formatted(
          dataSource,
          "%s_ToDafny(%s)".formatted(
              namespace.concat(resourceShape.toShapeId().getName()),
              dataSource
            )
        );
      }
    }

    //Handle @reference{Service} shape
    if (resourceOrService.asServiceShape().isPresent()) {
      var clientConversion = dataSource.concat(".DafnyClient");
      if (resourceOrService.hasTrait(ServiceTrait.class)) {
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            resourceOrService.toShapeId().getNamespace()
          ),
          DafnyNameResolver.dafnyTypesNamespace(resourceOrService)
        );
        final var shim =
          "%swrapped.Shim".formatted(
              DafnyNameResolver.dafnyNamespace(
                resourceOrService.expectTrait(ServiceTrait.class)
              )
            );
        clientConversion = "&%s{Client: %s}".formatted(shim, dataSource);
      }
      if (!this.isOptional) {
        return clientConversion;
      } else {
        final var goCodeBlock =
          """
          func () Wrappers.Option {
              if (%s) == nil {
              return Wrappers.Companion_Option_.Create_None_()
              }
              return Wrappers.Companion_Option_.Create_Some_(%s)
          }()""";
        return goCodeBlock.formatted(dataSource, clientConversion);
      }
    }

    throw new UnsupportedOperationException(
      "Unknown referenceStructureShape type: ".concat(shape.toString())
    );
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
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
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
    if (shape.hasTrait(ReferenceTrait.class)) {
      return referenceStructureShape(shape);
    }
    final var typeConversionMethodBuilder = new StringBuilder();
    writer.addImportFromModule(SMITHY_DAFNY_STD_LIB_GO, "Wrappers");
    writer.addImportFromModule(
      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
        shape.toShapeId().getNamespace()
      ),
      DafnyNameResolver.dafnyTypesNamespace(shape)
    );

    // Check if it's optional and needs to be wrapped in Wrappers.Some()
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

    //If it's a pointer type, we need to return nil/none instead of default value.
    var nilCheck = "";
    if (isPointerType) {
      nilCheck =
        "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
    }
    final String goCodeBlock;
    final String fieldSeparator;
    if (!shape.hasTrait(PositionalTrait.class)) {
      typeConversionMethodBuilder.append("%1$s(".formatted(companionStruct));
      goCodeBlock =
        """
        func () %s {
            %s
            return %s
        }()""";
      fieldSeparator = ",";
    } else {
      // Positional trait can only have one variable.
      fieldSeparator = "";
      // Don't unwrap position trait shape
      goCodeBlock =
        """
                %s
        """;
    }
    for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
      final var memberName = memberShapeEntry.getKey();
      final var memberShape = memberShapeEntry.getValue();
      typeConversionMethodBuilder.append(
        "%1$s%2$s".formatted(
            ShapeVisitorHelper.toDafnyShapeVisitorWriter(
              memberShape,
              context,
              dataSource.concat(".").concat(StringUtils.capitalize(memberName)),
              writer,
              isConfigShape,
              memberShape.isOptional(),
              context
                .symbolProvider()
                .toSymbol(memberShape)
                .getProperty(POINTABLE, Boolean.class)
                .orElse(false)
            ),
            fieldSeparator
          )
      );
    }
    if (shape.hasTrait(PositionalTrait.class)) {
      return goCodeBlock.formatted(typeConversionMethodBuilder.toString());
    }

    return goCodeBlock.formatted(
      returnType,
      nilCheck,
      someWrapIfRequired.formatted(
        typeConversionMethodBuilder.append(")").toString()
      )
    );
  }

  @Override
  public String mapShape(final MapShape shape) {
    final StringBuilder typeConversionMethodBuilder = new StringBuilder();

    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");

    final MemberShape keyMemberShape = shape.getKey();
    final MemberShape valueMemberShape = shape.getValue();
    String someWrapIfRequired = "%s";
    String returnType = "dafny.Map";
    if (this.isOptional) {
      someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
      returnType = "Wrappers.Option";
    }
    typeConversionMethodBuilder.append(
      """
      func () %s {
      	   fieldValue := dafny.NewMapBuilder()
      	   for key, val := range %s {
      		    fieldValue.Add(%s, %s)
      	   }
      	   return %s
      }()""".formatted(
          returnType,
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
    return typeConversionMethodBuilder.toString();
  }

  @Override
  public String listShape(final ListShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    final StringBuilder typeConversionMethodBuilder = new StringBuilder();
    final MemberShape memberShape = shape.getMember();
    String nilWrapIfRequired = "nil";
    String someWrapIfRequired = "%s";
    String returnType = "dafny.Sequence";
    var nilCheck = "";
    if (this.isOptional) {
      nilWrapIfRequired = "Wrappers.Companion_Option_.Create_None_()";
      nilCheck =
        "if %s == nil {return %s}".formatted(dataSource, nilWrapIfRequired);
      someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s)";
      returnType = "Wrappers.Option";
    }

    typeConversionMethodBuilder.append(
      """
      func () %s {
             %s
             var fieldValue []interface{} = make([]interface{}, 0)
             for _, val := range %s {
                 element := %s
                 fieldValue = append(fieldValue, element)
             }
             return %s
      }()""".formatted(
          returnType,
          nilCheck,
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
    return typeConversionMethodBuilder.toString();
  }

  @Override
  public String booleanShape(final BooleanShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    String nilWrapIfRequired = "nil";
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
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");

    // Enum is hard because we need to travers all the values, do an equal check and find the index.
    if (shape.hasTrait(EnumTrait.class)) {
      String nilWrapIfRequired = "nil";
      String someWrapIfRequired = "%s";
      String returnType = DafnyNameResolver.getDafnyType(
        shape,
        context.symbolProvider().toSymbol(shape)
      );
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
      return """
        func () %s {
        %s
      	var index int
      	for _, enumVal := range %s.Values() {
      		index++
      		if enumVal == %s%s{
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
          nilCheck,
          dataSource,
          dereferenceIfRequired,
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
      //It's a normal string shape (and not enum)
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
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    String nilWrapIfRequired = "nil";
    String someWrapIfRequired = "%s%s";
    String returnType = "int32";
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
    String nilWrapIfRequired = "nil";
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

    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");

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
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    writer.addUseImports(SmithyGoDependency.stdlib("encoding/binary"));
    writer.addUseImports(SmithyGoDependency.MATH);

    String nilWrapIfRequired = "nil";
    String someWrapIfRequired = "%s";
    String returnType = "float64";
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
    String someWrapIfRequired = "%s(%s)";
    String returnType = DafnyNameResolver.getDafnyType(
      shape,
      context.symbolProvider().toSymbol(shape)
    );

    String nilCheck = "";
    if (this.isOptional) {
      nilCheck =
        """
        if %s == nil {
          return Wrappers.Companion_Option_.Create_None_()
        }""".formatted(dataSource);
      someWrapIfRequired = "Wrappers.Companion_Option_.Create_Some_(%s(%s))";
      returnType = "Wrappers.Option";
    }

    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");

    final String functionInit =
      """
      func() %s {
          %s
          switch %s.(type) {""".formatted(returnType, nilCheck, dataSource);

    final StringBuilder eachMemberInUnion = new StringBuilder();
    for (final var member : shape.getAllMembers().values()) {
      final Shape targetShape = context.model().expectShape(member.getTarget());

      final var refShape = targetShape.hasTrait(ReferenceTrait.class)
        ? targetShape.expectTrait(ReferenceTrait.class).getReferentId()
        : null;

      final String baseType = refShape == null
        ? DafnyNameResolver.getDafnyType(
          targetShape,
          context.symbolProvider().toSymbol(targetShape)
        )
        : DafnyNameResolver.getDafnyType(
          context.model().expectShape(refShape),
          context
            .symbolProvider()
            .toSymbol(member)
            .getProperty("Referred", Symbol.class)
            .get()
        );

      eachMemberInUnion.append(
        """
        case *%s.%s:
            var inputToConversion = %s
            return %s
        """.formatted(
            SmithyNameResolver.smithyTypesNamespace(shape, context.model()),
            context.symbolProvider().toMemberName(member),
            ShapeVisitorHelper.toDafnyShapeVisitorWriter(
              member,
              context,
              dataSource +
              ".(*" +
              SmithyNameResolver.smithyTypesNamespace(shape, context.model()) +
              "." +
              context.symbolProvider().toMemberName(member) +
              ").Value",
              writer,
              isConfigShape,
              true, // Unions can't have required members otherwise they'll always end up taking the required type
              false
            ),
            someWrapIfRequired.formatted(
              DafnyNameResolver.getDafnyCreateFuncForUnionMemberShape(
                shape,
                member.getMemberName()
              ),
              "inputToConversion.UnwrapOr(nil).(%s)".formatted(baseType)
            )
          )
      );
    }

    final String defaultCase =
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
    writer.addImport("time");
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");

    String nilWrapIfRequired = "dafny.SeqOf()";
    String someWrapIfRequired = "%s";
    String returnType = "dafny.Sequence";
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

    var conversionCode =
      """
      func () %s {
        %s
        formattedTime := %s.Format(\"2006-01-02T15:04:05.999999Z\")
        return %s
      }()""".formatted(
          returnType,
          nilCheck,
          dataSource,
          someWrapIfRequired.formatted(
            "dafny.SeqOfChars([]dafny.Char(formattedTime)...)"
          )
        );
    return conversionCode;
  }
}
