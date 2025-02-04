package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import static software.amazon.polymorph.smithygo.utils.Constants.DAFNY_RUNTIME_GO_LIBRARY_MODULE;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.codegen.knowledge.GoPointableIndex;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithygo.utils.GoCodegenUtils;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
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
import software.amazon.smithy.utils.StringUtils;

/**
 * This class is used to generate the type conversion method for dafny to smithy / native shapes.
 * It uses the ShapeVisitor pattern to traverse the Smithy shapes and generate the corresponding Go type conversion code.
 */

// TODO: Remove anonymous function in each of the shape visitor and test if it will work
// TODO: if check with %s to figure out if it's a pointer or not and remove duplicate code when shape is optional vs non optional
// TODO: simple shapes could be migrated smithy-dafny-conversion library
public class DafnyToSmithyShapeVisitor extends ShapeVisitor.Default<String> {

  private final GenerationContext context;
  private final String dataSource;
  private final GoWriter writer;
  private final boolean isConfigShape;
  private final boolean isOptional;
  //TODO: Ideally this shouldn't be static but with current design we need to access this across instances.
  private static final Map<MemberShape, String> memberShapeConversionFuncMap =
    new LinkedHashMap<>();

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
    final boolean isOptional
  ) {
    this.context = context;
    this.dataSource = dataSource;
    this.writer = writer;
    this.isConfigShape = isConfigShape;
    this.isOptional = isOptional;
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
   * @param shape           MemberShape object.
   * @param conversionFunc  String representing the conversion function.
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
    if (resourceOrService.asResourceShape().isPresent()) {
      return referencedResourceShape(resourceOrService);
    }

    if (resourceOrService.asServiceShape().isPresent()) {
      return referencedServiceShape(resourceOrService);
    }

    throw new UnsupportedOperationException(
      "Unknown referenceStructureShape type: ".concat(shape.toString())
    );
  }

  /*
   * Return the conversion function for shapes with @reference{Service} trait.
   */
  private String referencedServiceShape(final Shape resourceOrService) {
    final var serviceShape = resourceOrService.asServiceShape().get();
    var namespace = "";
    if (
      !resourceOrService
        .toShapeId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSmithyNamespace(
          resourceOrService.toShapeId().getNamespace()
        ),
        SmithyNameResolver.shapeNamespace(serviceShape)
      );
      namespace =
        SmithyNameResolver.shapeNamespace(resourceOrService).concat(".");
    }
    if (serviceShape.hasTrait(ServiceTrait.class)) {
      writer.addImport(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          serviceShape.getId().getNamespace()
        )
      );
      return """
      shim, ok := %1$s.(*%2$swrapped.Shim)
      if !ok {
          panic("Not able to convert client to native")
      }
      return shim.Client
      """.formatted(
          dataSource,
          DafnyNameResolver.dafnyNamespace(
            resourceOrService.expectTrait(ServiceTrait.class)
          )
        );
    }
    if (!this.isOptional) {
      return """
      value, ok := %s.(%s)
      if !ok {
        panic("invalid type found.")
      }
      return &%s{value}
      """.formatted(
          dataSource,
          DafnyNameResolver.getDafnyInterfaceClient(serviceShape),
          namespace.concat(
            context.symbolProvider().toSymbol(serviceShape).getName()
          )
        );
    }
    return """
    return func () *%s {
        if %s == nil {
            return nil;
        }
        value, ok := %s.(%s)
        if !ok {
          panic("invalid type found.")
        }
        return &%s{value}
    }()""".formatted(
        namespace.concat(
          context.symbolProvider().toSymbol(serviceShape).getName()
        ),
        dataSource,
        dataSource,
        DafnyNameResolver.getDafnyInterfaceClient(serviceShape),
        namespace.concat(
          context.symbolProvider().toSymbol(serviceShape).getName()
        )
      );
  }

  /*
   * Return the conversion function for shapes with @reference{Resource} trait.
   */
  private String referencedResourceShape(final Shape resourceOrService) {
    final var resourceShape = resourceOrService.asResourceShape().get();
    var namespace = "";
    if (
      !resourceOrService
        .toShapeId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSmithyNamespace(
          resourceOrService.toShapeId().getNamespace()
        ),
        SmithyNameResolver.shapeNamespace(resourceShape)
      );
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSmithyNamespace(
          resourceOrService.toShapeId().getNamespace()
        ),
        SmithyNameResolver.smithyTypesNamespace(resourceShape, context.model())
      );
      namespace =
        SmithyNameResolver.shapeNamespace(resourceOrService).concat(".");
    }
    if (!this.isOptional) {
      return "%s_FromDafny(%s)".formatted(
          namespace.concat(resourceShape.toShapeId().getName()),
          dataSource
        );
    }
    return """
    func () %s.I%s {
        if %s == nil {
            return nil;
        }
        return %s
    }()""".formatted(
        SmithyNameResolver.smithyTypesNamespace(resourceShape, context.model()),
        resourceShape.getId().getName(),
        dataSource,
        "%s_FromDafny(%s.(%s.I%s))".formatted(
            namespace.concat(resourceShape.toShapeId().getName()),
            dataSource,
            DafnyNameResolver.dafnyTypesNamespace(resourceShape),
            resourceShape.getId().getName()
          )
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
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    // Blob shape is inherently value type
    return """
    return func () []byte {
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
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }
    if (shape.hasTrait(ReferenceTrait.class)) {
      return referenceStructureShape(shape);
    }

    writer.addImportFromModule(
      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
        shape.toShapeId().getNamespace()
      ),
      DafnyNameResolver.dafnyTypesNamespace(shape)
    );

    // Optional values in Dafny use Wrappers.None but Go doesn't have not-set convention
    // for value types. Hence we use pointer-types in Go which needs to be passed using reference.
    final String referenceType = (this.isOptional) ? "&" : "";

    final var typeConversionMethodBuilder = new StringBuilder();
    if (this.isOptional) {
      final String unAssertedDataSource = dataSource.startsWith("input.(")
        ? "input"
        : dataSource;
      typeConversionMethodBuilder.append(
        """
          if %s == nil {
              return nil
          }
        """.formatted(unAssertedDataSource)
      );
    }
    typeConversionMethodBuilder.append(
      "return %1$s%2$s{".formatted(
          referenceType,
          SmithyNameResolver
            .smithyTypesNamespace(shape, context.model())
            .concat(".")
            .concat(shape.getId().getName())
        )
    );

    // Visit each of the member shapes in the structure and get the conversion function for them
    for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
      final var memberName = memberShapeEntry.getKey();
      final var memberShape = memberShapeEntry.getValue();
      final var targetShape = context
        .model()
        .expectShape(memberShape.getTarget());
      final String DtorConversion;
      if (!shape.hasTrait(PositionalTrait.class)) {
        DtorConversion =
          ".Dtor_%s()".formatted(
              DafnyNameResolver.dafnyCompilesExtra_(memberName)
            );
      } else {
        // Shapes with PositionalTrait already gets input unwrapped so no conversion needed.
        DtorConversion = "";
      }

      // If a value is a generic type or optional, we need type casting. Dafny doesn't support generics yet.
      //TODO: Is it ever possible for structure to be nil?
      String maybeAssertion = "";
      if (dataSource.equals("input")) {
        maybeAssertion =
          ".(".concat(
              DafnyNameResolver.getDafnyType(
                shape,
                context.symbolProvider().toSymbol(shape)
              )
            )
            .concat(")");
      }
      final boolean assertionRequired =
        memberShape.isOptional() &&
        targetShape.isStructureShape() &&
        !targetShape.hasTrait(ReferenceTrait.class);
      final var derivedDataSource =
        "%1$s%2$s%3$s%4$s".formatted(
            dataSource,
            maybeAssertion,
            DtorConversion,
            memberShape.isOptional() ? ".UnwrapOr(nil)" : ""
          );

      typeConversionMethodBuilder.append(
        """
           %1$s: %2$s,
        """.formatted(
            StringUtils.capitalize(memberName),
            ShapeVisitorHelper.toNativeShapeVisitorWriter(
              memberShape,
              context,
              derivedDataSource,
              assertionRequired,
              writer,
              isConfigShape,
              memberShape.isOptional()
            )
          )
      );
    }

    return typeConversionMethodBuilder.append("}").toString();
  }

  // TODO: smithy-dafny-conversion library
  @Override
  public String listShape(final ListShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }
    final StringBuilder typeConversionMethodBuilder = new StringBuilder();
    final MemberShape memberShape = shape.getMember();
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());
    final var symbol = context.symbolProvider().toSymbol(shape);
    final boolean assertionRequired = targetShape.isStructureShape();
    if (isOptional) {
      typeConversionMethodBuilder.append(
        """
        if %s == nil {
          return nil
        }
        """.formatted(dataSource)
      );
    }
    typeConversionMethodBuilder.append(
      """
      fieldValue := make(%s, 0)
      for i := dafny.Iterate(%s.(dafny.Sequence)); ; {
      	val, ok := i()
      	if !ok {
      		break
      	}
      	fieldValue = append(fieldValue, %s)}
      	""".formatted(
          GoCodegenUtils.getType(symbol, true, context.model()),
          dataSource,
          ShapeVisitorHelper.toNativeShapeVisitorWriter(
            memberShape,
            context,
            "val",
            assertionRequired,
            writer,
            isConfigShape,
            false
          )
        )
    );
    // Close structure
    return typeConversionMethodBuilder.append("return fieldValue").toString();
  }

  @Override
  public String mapShape(final MapShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }
    final StringBuilder typeConversionMethodBuilder = new StringBuilder();
    final MemberShape keyMemberShape = shape.getKey();
    final MemberShape valueMemberShape = shape.getValue();
    final Shape valueTargetShape = context
      .model()
      .expectShape(valueMemberShape.getTarget());
    final var type = SmithyNameResolver.getSmithyType(
      valueTargetShape,
      context.symbolProvider().toSymbol(valueTargetShape),
      context.model()
    );
    final String valueDataSource = "(*val.(dafny.Tuple).IndexInt(1))";
    typeConversionMethodBuilder.append(
      """
      var m map[string]%s = make(map[string]%s)
      if %s == nil {
          return nil
      }
      for i := dafny.Iterate(%s.(dafny.Map).Items());; {
      	val, ok := i()
      	if !ok {
      		break;
      	}
      	m[%s] = %s
      }
      return m
      """.formatted(
          type,
          type,
          dataSource,
          dataSource,
          ShapeVisitorHelper.toNativeShapeVisitorWriter(
            keyMemberShape,
            context,
            "(*val.(dafny.Tuple).IndexInt(0))",
            false,
            writer,
            isConfigShape,
            false
          ),
          ShapeVisitorHelper.toNativeShapeVisitorWriter(
            valueMemberShape,
            context,
            valueDataSource,
            false,
            writer,
            isConfigShape,
            false
          )
        )
    );
    return typeConversionMethodBuilder.toString();
  }

  @Override
  public String booleanShape(final BooleanShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }
    if (this.isOptional) {
      return """
      return func() *bool {
          var b bool
          if %s == nil {
              return nil
          }
          b = %s.(%s)
          return &b
      }()""".formatted(
          dataSource,
          dataSource,
          context.symbolProvider().toSymbol(shape).getName()
        );
    } else {
      return "return %s.(%s)".formatted(
          dataSource,
          context.symbolProvider().toSymbol(shape).getName()
        );
    }
  }

  @Override
  public String stringShape(final StringShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }
    if (shape.hasTrait(EnumTrait.class)) {
      if (
        !shape
          .toShapeId()
          .getNamespace()
          .equals(context.settings().getService().getNamespace())
      ) {
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            shape.toShapeId().getNamespace()
          ),
          DafnyNameResolver.dafnyTypesNamespace(shape)
        );
      }
      if (this.isOptional) {
        return """
          return func () *%s.%s {
          var u %s.%s
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
        }()""".formatted(
            SmithyNameResolver.smithyTypesNamespace(shape, context.model()),
            context.symbolProvider().toSymbol(shape).getName(),
            SmithyNameResolver.smithyTypesNamespace(shape, context.model()),
            context.symbolProvider().toSymbol(shape).getName(),
            dataSource,
            dataSource,
            DafnyNameResolver.getDafnyType(
              shape,
              context.symbolProvider().toSymbol(shape)
            ),
            DafnyNameResolver.getDafnyCompanionStructType(
              shape,
              context.symbolProvider().toSymbol(shape)
            ),
            DafnyNameResolver.getDafnyType(
              shape,
              context.symbolProvider().toSymbol(shape)
            )
          );
      } else {
        return """
          return func () %s.%s {
          var u %s.%s
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
        }()""".formatted(
            SmithyNameResolver.smithyTypesNamespace(shape, context.model()),
            context.symbolProvider().toSymbol(shape).getName(),
            SmithyNameResolver.smithyTypesNamespace(shape, context.model()),
            context.symbolProvider().toSymbol(shape).getName(),
            dataSource,
            DafnyNameResolver.getDafnyType(
              shape,
              context.symbolProvider().toSymbol(shape)
            ),
            DafnyNameResolver.getDafnyCompanionStructType(
              shape,
              context.symbolProvider().toSymbol(shape)
            ),
            DafnyNameResolver.getDafnyType(
              shape,
              context.symbolProvider().toSymbol(shape)
            )
          );
      }
    }

    //Handle the @utf8Bytes Trait
    final var underlyingType = shape.hasTrait(DafnyUtf8BytesTrait.class)
      ? "uint8"
      : "dafny.Char";
    var strConv = "s = s + string(val.(%s))".formatted(underlyingType);
    if (underlyingType.equals("uint8")) {
      strConv =
        """
            // UTF bytes should be always converted from bytes to string in go
            // Otherwise go treats the string as a unicode codepoint

            var valUint, _ = val.(%s)
            var byteSlice = []byte{valUint}
            s = s + string(byteSlice)
        """.formatted(underlyingType);
    }

    if (isOptional) {
      return """
       return func() (*string) {
           var s string
       if %s == nil {
           return nil
       }
           for i := dafny.Iterate(%s) ; ; {
               val, ok := i()
               if !ok {
                   return &[]string{s}[0]
               } else {
                   %s
               }
          }
      }()""".formatted(dataSource, dataSource, strConv);
    } else {
      return """
       return func() (string) {
           var s string
           for i := dafny.Iterate(%s) ; ; {
               val, ok := i()
               if !ok {
                   return s
               } else {
                   %s
               }
          }
      }()""".formatted(dataSource, strConv);
    }
  }

  @Override
  public String integerShape(final IntegerShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }
    if (isOptional) {
      return (
        """
        return func() *int32 {
            var b int32
            if %s == nil {
                return nil
            }
            b = %s.(int32)
            return &b
        }()""".formatted(dataSource, dataSource)
      );
    } else {
      return """
      return func() int32 {
          var b = %s.(int32)
          return b
      }()""".formatted(dataSource);
    }
  }

  @Override
  public String longShape(final LongShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }
    if (isOptional) {
      return (
        """
        return func() *int64 {
            var b int64
            if %s == nil {
                return nil
            }
            b = %s.(int64)
            return &b
        }()"""
      ).formatted(dataSource, dataSource);
    } else {
      return """
      return func() int64 {
          var b = %s.(int64)
          return b
      }()
          """.formatted(dataSource);
    }
  }

  @Override
  public String doubleShape(final DoubleShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }
    writer.addUseImports(SmithyGoDependency.MATH);
    if (isOptional) {
      return """
      return func () *float64 {
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
    } else {
      return """
      return func () float64 {
          var b []byte
          for i := dafny.Iterate(%s) ; ; {
              val, ok := i()
      	    if !ok {
            return []float64{math.Float64frombits(binary.LittleEndian.Uint64(b))}[0]
           } else {
            b = append(b, val.(byte))
           }
          }
      }()""".formatted(dataSource);
    }
  }

  @Override
  public String unionShape(final UnionShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    if (SmithyNameResolver.isShapeFromAWSSDK(shape)) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSdkNamespace(
          shape.getId().getNamespace()
        ),
        "types",
        SmithyNameResolver.smithyTypesNamespace(shape, context.model())
      );
    }

    String nilCheck = "";
    if (isOptional) {
      nilCheck =
        """
        if %s == nil {
                return nil
        }""".formatted(dataSource);
    }

    final String functionInit =
      """
          var union %s
          %s
      """.formatted(context.symbolProvider().toSymbol(shape), nilCheck);

    final StringBuilder eachMemberInUnion = new StringBuilder();
    for (final var member : shape.getAllMembers().values()) {
      final Shape targetShape = context.model().expectShape(member.getTarget());
      final String memberName = context.symbolProvider().toMemberName(member);

      final String rawUnionDataSource =
        "(" +
        dataSource +
        ".(" +
        DafnyNameResolver.getDafnyType(
          shape,
          context.symbolProvider().toSymbol(shape)
        ) +
        "))";

      // unwrap union type, assert it then convert it to its member type with Dtor_ (example: Dtor_BlobValue()). unionDataSource is not a wrapper object until now.
      String unionDataSource =
        rawUnionDataSource +
        ".Dtor_%s()".formatted(
            DafnyNameResolver.dafnyCompilesExtra_(member.getMemberName())
          );
      final boolean isMemberShapePointable =
        (GoPointableIndex.of(context.model()).isPointable(member)) &&
        !targetShape.isStructureShape();
      final String pointerForPointableShape = isMemberShapePointable ? "*" : "";
      final String isMemberCheck =
        "if ((%s).Is_%s()) {".formatted(
            rawUnionDataSource,
            DafnyNameResolver.dafnyCompilesExtra_(member.getMemberName())
          );

      String wrappedDataSource = "";
      boolean requireAssertion = true;
      if (!(targetShape.isStructureShape())) {
        // All other shape except structure needs a Wrapper object but unionDataSource is not a Wrapper object.
        wrappedDataSource =
          "var dataSource = Wrappers.Companion_Option_.Create_Some_(%s)".formatted(
              unionDataSource
            );
        unionDataSource = "dataSource.UnwrapOr(nil)";
        requireAssertion = false;
      }

      eachMemberInUnion.append(
        """
        %s
        %s
        union = &%s.%s{
                Value: %s(%s),
            }
        }
        """.formatted(
            isMemberCheck,
            wrappedDataSource,
            SmithyNameResolver.smithyTypesNamespace(shape, context.model()),
            memberName,
            pointerForPointableShape,
            ShapeVisitorHelper.toNativeShapeVisitorWriter(
              member,
              context,
              unionDataSource,
              requireAssertion,
              writer,
              isConfigShape,
              isMemberShapePointable
            )
          )
      );
    }

    return """
        %s
        %s
        return union
    """.formatted(functionInit, eachMemberInUnion);
  }

  @Override
  public String timestampShape(final TimestampShape shape) {
    writer.addImport("time");
    if (isOptional) {
      return """
      	return func() *time.Time {
      	var s string
      	if %s == nil {
      		return nil
      	}
      	for i := dafny.Iterate(%s.(dafny.Sequence)); ; {
      		val, ok := i()
      		if !ok {
      			break
      		} else {
      			s = s + string(val.(dafny.Char))
      		}
      	}
      	if len(s) == 0 {
      		return nil
      	} else {
      		t, err := time.Parse("2006-01-02T15:04:05.999999Z", s)
      		if err != nil {
      			panic(err)
      		}
      		return &t
      	}
      }()""".formatted(dataSource, dataSource);
    } else {
      return """
      	return func() time.Time {
      	var s string

      	for i := dafny.Iterate(%s); ; {
      		val, ok := i()
      		if !ok {
      			break
      		} else {
      			s = s + string(val.(dafny.Char))
      		}
      	}
      	if len(s) == 0 {
      		panic("timestamp string is empty")
      	} else {
      		t, err := time.Parse("2006-01-02T15:04:05.999999Z", s)
      		if err != nil {
      			panic(err)
      		}
      		return t
      	}
      }()""".formatted(dataSource);
    }
  }
}
