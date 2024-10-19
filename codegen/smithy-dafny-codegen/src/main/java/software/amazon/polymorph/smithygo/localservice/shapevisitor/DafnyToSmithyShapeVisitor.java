package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;
import static software.amazon.polymorph.smithygo.utils.Constants.DAFNY_RUNTIME_GO_LIBRARY_MODULE;

import java.util.HashMap;
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
import software.amazon.polymorph.traits.ReferenceTrait;
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
import software.amazon.smithy.utils.StringUtils;

// TODO: Remove anonymous function in each of the shape visitor and test if it will work
// TODO: if check with %s to figure out if it's a pointer or not and remove duplicate code when shape is optional vs non optional
public class DafnyToSmithyShapeVisitor extends ShapeVisitor.Default<String> {

  private final GenerationContext context;
  private final String dataSource;
  private final GoWriter writer;
  private final boolean isConfigShape;
  private final boolean isOptional;
  //TODO: Ideally this shouldn't be static but with current design we need to access this across instances.
  private static final Map<MemberShape, String> memberShapeConversionFuncMap =
    new HashMap<>();

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

  public static Set<MemberShape> getAllShapesRequiringConversionFunc() {
    return memberShapeConversionFuncMap.keySet();
  }

  public static void putShapesWithConversionFunc(
    final MemberShape shape,
    final String conversionFunc
  ) {
    memberShapeConversionFuncMap.put(shape, conversionFunc);
  }

  public static String getConversionFunc(final MemberShape shape) {
    return memberShapeConversionFuncMap.get(shape);
  }

  protected String referenceStructureShape(final StructureShape shape) {
    final ReferenceTrait referenceTrait = shape.expectTrait(
      ReferenceTrait.class
    );
    final Shape resourceOrService = context
      .model()
      .expectShape(referenceTrait.getReferentId());
    var namespace = "";
    if (resourceOrService.asResourceShape().isPresent()) {
      final var resourceShape = resourceOrService.asResourceShape().get();
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
          SmithyNameResolver.smithyTypesNamespace(resourceShape),
          resourceShape.getId().getName(),
          dataSource,
          "%s_FromDafny(%s.(%s.I%s))".formatted(
              namespace.concat(resourceShape.toShapeId().getName()),
              dataSource,
              DafnyNameResolver.dafnyTypesNamespace(resourceShape),
              resourceShape.getId().getName()
            )
        );
    } else {
      final var serviceShape = resourceOrService.asServiceShape().get();
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
      if (!this.isOptional) {
        return "return %1$s{%2$s}".formatted(
            namespace.concat(
              context.symbolProvider().toSymbol(serviceShape).getName()
            ),
            dataSource
          );
      }
      return """
      return func () *%s {
          if %s == nil {
              return nil;
          }
          return &%s{%s.(*%s)}
      }()""".formatted(
          namespace.concat(
            context.symbolProvider().toSymbol(serviceShape).getName()
          ),
          dataSource,
          namespace.concat(
            context.symbolProvider().toSymbol(serviceShape).getName()
          ),
          dataSource,
          DafnyNameResolver.getDafnyClient(serviceShape.toShapeId().getName())
        );
    }
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
    if (shape.hasTrait(ReferenceTrait.class)) {
      return referenceStructureShape(shape);
    }
    final var builder = new StringBuilder();
    writer.addImportFromModule(
      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
        shape.toShapeId().getNamespace()
      ),
      DafnyNameResolver.dafnyTypesNamespace(shape)
    );
    final String referenceType = (this.isOptional) ? "&" : "";
    builder.append(
      "return %1$s%2$s{".formatted(
          referenceType,
          SmithyNameResolver
            .smithyTypesNamespace(shape)
            .concat(".")
            .concat(shape.getId().getName())
        )
    );
    for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
      final var memberName = memberShapeEntry.getKey();
      final var memberShape = memberShapeEntry.getValue();
      final var targetShape = context
        .model()
        .expectShape(memberShape.getTarget());
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
        "%1$s%2$s%3$s%4$s%5$s".formatted(
            dataSource,
            maybeAssertion,
            ".Dtor_%s()".formatted(memberName),
            memberShape.isOptional() ? ".UnwrapOr(nil)" : "",
            assertionRequired
              ? ".(%s)".formatted(
                  DafnyNameResolver.getDafnyType(
                    targetShape,
                    context.symbolProvider().toSymbol(memberShape)
                  )
                )
              : ""
          );
      builder.append(
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

    return builder.append("}").toString();
  }

  // TODO: smithy-dafny-conversion library
  @Override
  public String listShape(final ListShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    final StringBuilder builder = new StringBuilder();
    final MemberShape memberShape = shape.getMember();
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());
    final var symbol = context.symbolProvider().toSymbol(shape);
    final Boolean assertionRequired = targetShape.isStructureShape();
    builder.append(
      """
                           var fieldValue %s
                    if %s == nil {
                        return nil
                    }
      for i := dafny.Iterate(%s.(dafny.Sequence)); ; {
      	val, ok := i()
      	if !ok {
      		break
      	}
      	fieldValue = append(fieldValue, %s)}
      	""".formatted(
          GoCodegenUtils.getType(symbol, shape),
          dataSource,
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
    return builder.append("return fieldValue").toString();
  }

  @Override
  public String mapShape(final MapShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    final StringBuilder builder = new StringBuilder();
    final MemberShape keyMemberShape = shape.getKey();
    final MemberShape valueMemberShape = shape.getValue();
    final Shape valueTargetShape = context
      .model()
      .expectShape(valueMemberShape.getTarget());
    final var type = SmithyNameResolver.getSmithyType(
      valueTargetShape,
      context.symbolProvider().toSymbol(valueTargetShape)
    );
    final String valueDataSource = "(*val.(dafny.Tuple).IndexInt(1))";
    builder.append(
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
    return builder.toString();
  }

  @Override
  public String booleanShape(final BooleanShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
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
    if (shape.hasTrait(EnumTrait.class)) {
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
          SmithyNameResolver.smithyTypesNamespace(shape),
          context.symbolProvider().toSymbol(shape).getName(),
          SmithyNameResolver.smithyTypesNamespace(shape),
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
    }

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
        ".Dtor_" +
        memberName.replace(shape.getId().getName().concat("Member"), "") +
        "()";
      final boolean isMemberShapePointable =
        (GoPointableIndex.of(context.model()).isPointable(member)) &&
        !targetShape.isStructureShape();
      final String pointerForPointableShape = isMemberShapePointable ? "*" : "";
      final String isMemberCheck =
        "if ((%s).%s()) {".formatted(
            rawUnionDataSource,
            memberName.replace(shape.getId().getName().concat("Member"), "Is_")
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
            SmithyNameResolver.smithyTypesNamespace(shape),
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
    // TODO: Figure out timestamp types when working on timestampShape
    writer.addImport("time");
    return "nil";
  }
}
