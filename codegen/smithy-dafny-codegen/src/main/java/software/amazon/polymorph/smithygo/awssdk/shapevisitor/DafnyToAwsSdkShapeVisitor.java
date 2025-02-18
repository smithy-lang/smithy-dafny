package software.amazon.polymorph.smithygo.awssdk.shapevisitor;

import static software.amazon.polymorph.smithygo.utils.Constants.DAFNY_RUNTIME_GO_LIBRARY_MODULE;
import static software.amazon.polymorph.smithygo.utils.Constants.SMITHY_DAFNY_STD_LIB_GO;

import java.util.*;
import software.amazon.polymorph.smithygo.awssdk.AwsSdkGoPointableIndex;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.codegen.Synthetic;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithygo.utils.GoCodegenUtils;
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
public class DafnyToAwsSdkShapeVisitor extends ShapeVisitor.Default<String> {

  private final AwsSdkGoPointableIndex awsSdkGoPointableIndex;
  private final GenerationContext context;
  private final String dataSource;
  private final GoWriter writer;
  private final ServiceTrait serviceTrait;
  private final boolean isOptional;
  private final boolean isPointable;

  //TODO: Ideally this shouldn't be static but with current design we need to access this across instances.
  private static final Map<MemberShape, String> memberShapeConversionFuncMap =
    new LinkedHashMap<>();

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
    this.serviceTrait =
      context
        .model()
        .expectShape(context.settings().getService(context.model()).toShapeId())
        .getTrait(ServiceTrait.class)
        .get();
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
    final String unAssertedDataSource = dataSource.startsWith("input.(")
      ? "input"
      : dataSource;
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
    }()""".formatted(unAssertedDataSource, dataSource);
  }

  @Override
  public String structureShape(final StructureShape shape) {
    final var typeConversionMethodBuilder = new StringBuilder();

    writer.addImportFromModule(
      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
        shape.toShapeId().getNamespace()
      ),
      DafnyNameResolver.dafnyTypesNamespace(shape)
    );

    // If it's contained within another shape - decided from where to import the symbol
    final var subtype =
      !(awsSdkGoPointableIndex.isOperationStruct(shape) ||
        shape.hasTrait(Synthetic.class)) ||
      shape.toShapeId().getName().contains("Exception");

    var nilcheck = "";
    if (this.isOptional) {
      if (this.isPointable) {
        final String unAssertedDataSource = dataSource.startsWith("input.(")
          ? "input"
          : dataSource;
        nilcheck =
          "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
        nilcheck = "";
      }
    }

    typeConversionMethodBuilder.append(
      """
      func() %s%s {
      %s
      return %s%s {
      """.formatted(
          this.isPointable ? "*" : "",
          SmithyNameResolver
            .smithyTypesNamespaceAws(serviceTrait, subtype)
            .concat(".")
            .concat(shape.getId().getName()),
          nilcheck,
          this.isPointable ? "&" : "",
          SmithyNameResolver
            .smithyTypesNamespaceAws(serviceTrait, subtype)
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

      final var assertionRequired = memberShape.isOptional();
      final var derivedDataSource =
        "%1$s%2$s%3$s%4$s".formatted(
            dataSource,
            maybeAssertion,
            ".Dtor_%s()".formatted(memberName),
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
              memberShape.isOptional(),
              awsSdkGoPointableIndex.isPointable(targetShape)
            )
          )
      );
    }

    return typeConversionMethodBuilder.append("}}()").toString();
  }

  // TODO: smithy-dafny-conversion library
  @Override
  public String listShape(final ListShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    final StringBuilder typeConversionMethodBuilder = new StringBuilder();
    final MemberShape memberShape = shape.getMember();

    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());

    final var typeName = GoCodegenUtils.getType(
      context.symbolProvider().toSymbol(targetShape),
      serviceTrait,
      true
    );

    final String unAssertedDataSource = dataSource.startsWith("input.(")
      ? "input"
      : dataSource;

    typeConversionMethodBuilder.append(
      """
      func() []%s{
          var fieldValue []%s
          %s
          for i := dafny.Iterate(%s.(dafny.Sequence)); ; {
           val, ok := i()
           if !ok {
               break
           }
           fieldValue = append(fieldValue, %s)}
      """.formatted(
          typeName,
          typeName,
          this.isOptional
            ? """
            if %s == nil {
                return nil
            }""".formatted(unAssertedDataSource)
            : "",
          dataSource,
          ShapeVisitorHelper.toNativeShapeVisitorWriter(
            memberShape,
            context,
            "val",
            memberShape.isOptional(),
            writer,
            false,
            awsSdkGoPointableIndex.isPointable(memberShape)
          )
        )
    );

    // Close structure
    return typeConversionMethodBuilder
      .append("return fieldValue }()")
      .toString();
  }

  @Override
  public String mapShape(final MapShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    final StringBuilder typeConversionMethodBuilder = new StringBuilder();
    final MemberShape keyMemberShape = shape.getKey();

    final MemberShape valueMemberShape = shape.getValue();
    final Shape valueTargetShape = context
      .model()
      .expectShape(valueMemberShape.getTarget());
    final var typeName = GoCodegenUtils.getType(
      context.symbolProvider().toSymbol(valueTargetShape),
      serviceTrait,
      true
    );

    var nilCheck = "";
    final String unAssertedDataSource = dataSource.startsWith("input.(")
      ? "input"
      : dataSource;
    if (this.isOptional) {
      nilCheck =
        """
        if %s == nil {
            return nil
        }
        """.formatted(unAssertedDataSource);
    }
    typeConversionMethodBuilder.append(
      """
      func() map[string]%s {
          var m map[string]%s = make(map[string]%s)
          %s
          for i := dafny.Iterate(%s.(dafny.Map).Items());; {
              val, ok := i()
           	  if !ok {
           	      break;
           	  }
           	  m[%s] = %s
          }
          return m
      }()""".formatted(
          typeName,
          typeName,
          typeName,
          nilCheck,
          unAssertedDataSource,
          ShapeVisitorHelper.toNativeShapeVisitorWriter(
            keyMemberShape,
            context,
            "(*val.(dafny.Tuple).IndexInt(0))",
            false,
            writer,
            keyMemberShape.isOptional(),
            awsSdkGoPointableIndex.isPointable(keyMemberShape)
          ),
          ShapeVisitorHelper.toNativeShapeVisitorWriter(
            valueMemberShape,
            context,
            "(*val.(dafny.Tuple).IndexInt(1))",
            valueMemberShape.isOptional(),
            writer,
            false,
            awsSdkGoPointableIndex.isPointable(valueMemberShape)
          )
        )
    );
    return typeConversionMethodBuilder.toString();
  }

  @Override
  public String booleanShape(final BooleanShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    var nilCheck = "";
    final String unAssertedDataSource = dataSource.startsWith("input.(")
      ? "input"
      : dataSource;
    if (this.isOptional) {
      if (this.isPointable) {
        nilCheck =
          "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
        nilCheck = "if %s == nil { return b }".formatted(unAssertedDataSource);
      }
    }
    return """
    func() %sbool {
        var b bool
        %s
        b = %s.(bool)
        return %sb
    }()""".formatted(
        this.isPointable ? "*" : "",
        nilCheck,
        unAssertedDataSource,
        this.isPointable ? "&" : ""
      );
  }

  @Override
  public String stringShape(final StringShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");

    if (shape.hasTrait(EnumTrait.class)) {
      var nilCheck = "";

      if (this.isOptional) {
        final var unAssertedDataSource = dataSource.startsWith("input.(")
          ? "input"
          : dataSource;
        nilCheck =
          """
          if %s == nil {
                return u
            }
          """.formatted(unAssertedDataSource);
      }

      return """
         func () %s.%s {
         var u %s.%s
         %s
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
          SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, true),
          context.symbolProvider().toSymbol(shape).getName(),
          SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, true),
          context.symbolProvider().toSymbol(shape).getName(),
          nilCheck,
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

    //Handle the @utf8Bytes Trait
    final var underlyingType = shape.hasTrait(DafnyUtf8BytesTrait.class)
      ? "uint8"
      : "dafny.Char";

    var nilCheck = "";
    final String unAssertedDataSource = dataSource.startsWith("input.(")
      ? "input"
      : dataSource;

    if (this.isOptional) {
      if (this.isPointable) {
        nilCheck =
          "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
        nilCheck = "if %s == nil { return s }".formatted(unAssertedDataSource);
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
    }()""".formatted(
        this.isPointable ? "*" : "",
        nilCheck,
        dataSource,
        this.isPointable ? "&" : "",
        underlyingType
      );
  }

  @Override
  public String integerShape(final IntegerShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    if (AwsSdkGoPointableIndex.of(context.model()).isPointable(shape)) {
      final String unAssertedDataSource = dataSource.startsWith("input.(")
        ? "input"
        : dataSource;
      return """
      func() *int32 {
          var i int32
          if %s == nil {
              return nil
          }
          i = %s
          return &i
      }()""".formatted(unAssertedDataSource, dataSource);
    } else {
      return "%s".formatted(dataSource);
    }
  }

  @Override
  public String longShape(final LongShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    var nilCheck = "";
    final String unAssertedDataSource = dataSource.startsWith("input.(")
      ? "input"
      : dataSource;
    if (this.isOptional) {
      if (this.isPointable) {
        nilCheck =
          "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
        nilCheck = "if %s == nil { return i}".formatted(unAssertedDataSource);
      }
    }
    return """
    func() %sint64 {
        var i int64
        %s
        i = %s.(int64)
        return %si
    }()""".formatted(
        this.isPointable ? "*" : "",
        nilCheck,
        unAssertedDataSource,
        this.isPointable ? "&" : ""
      );
  }

  @Override
  public String doubleShape(final DoubleShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    writer.addUseImports(SmithyGoDependency.MATH);
    writer.addUseImports(SmithyGoDependency.stdlib("encoding/binary"));
    var nilCheck = "";

    if (this.isOptional) {
      final String unAssertedDataSource = dataSource.startsWith("input.(")
        ? "input"
        : dataSource;
      if (this.isPointable) {
        nilCheck =
          "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
        nilCheck =
          "if %s == nil { var f float64; return f}".formatted(
              unAssertedDataSource
            );
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
    }()""".formatted(
        this.isPointable ? "*" : "",
        nilCheck,
        dataSource,
        this.isPointable ? "&" : ""
      );
  }

  @Override
  public String unionShape(final UnionShape shape) {
    writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
    writer.addImportFromModule(SMITHY_DAFNY_STD_LIB_GO, "Wrappers");

    var nilCheck = "";
    if (this.isOptional) {
      final String unAssertedDataSource = dataSource.startsWith("input.(")
        ? "input"
        : dataSource;
      if (this.isPointable) {
        nilCheck =
          "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
        nilCheck =
          "if %s == nil { return union}".formatted(unAssertedDataSource);
      }
    }

    final var functionInit =
      """
      func() %s {
          var union %s
          %s
      """.formatted(
          SmithyNameResolver.getSmithyTypeAws(
            serviceTrait,
            context.symbolProvider().toSymbol(shape),
            true
          ),
          SmithyNameResolver.getSmithyTypeAws(
            serviceTrait,
            context.symbolProvider().toSymbol(shape),
            true
          ),
          nilCheck
        );

    final var eachMemberInUnion = new StringBuilder();
    for (final var member : shape.getAllMembers().values()) {
      final var targetShape = context.model().expectShape(member.getTarget());
      final var memberName = context.symbolProvider().toMemberName(member);

      // unwrap union type, assert it then convert it to its member type with Dtor_ (example: Dtor_BlobValue()). unionDataSource is not a wrapper object until now.
      var unionDataSource = dataSource.concat(
        ".Dtor_%s()".formatted(
            DafnyNameResolver.dafnyCompilesExtra_(member.getMemberName())
          )
      );
      final var isMemberShapePointable = awsSdkGoPointableIndex.isPointable(
        member
      );
      final var pointerForPointableShape = isMemberShapePointable ? "*" : "";
      final var isMemberCheck =
        "if ((%s).Is_%s()) {".formatted(
            dataSource,
            DafnyNameResolver.dafnyCompilesExtra_(member.getMemberName())
          );

      var wrappedDataSource = "";
      var requiresAssertion = true;

      if (!(targetShape.isStructureShape())) {
        // All other shape except structure needs a Wrapper object but unionDataSource is not a Wrapper object.
        wrappedDataSource =
          """
          var dataSource = Wrappers.Companion_Option_.Create_Some_(%s)""".formatted(
              unionDataSource
            );
        unionDataSource = "dataSource.UnwrapOr(nil)";
        requiresAssertion = false;
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
            SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, true),
            memberName,
            pointerForPointableShape,
            ShapeVisitorHelper.toNativeShapeVisitorWriter(
              member,
              context,
              unionDataSource,
              requiresAssertion,
              writer,
              member.isOptional(),
              isMemberShapePointable
            )
          )
      );
    }
    return """
        %s
        %s
        return union
    }()""".formatted(functionInit, eachMemberInUnion);
  }

  @Override
  public String timestampShape(final TimestampShape shape) {
    writer.addImport("time");

    var nilCheck = "";
    final String unAssertedDataSource = dataSource.startsWith("input.(")
      ? "input"
      : dataSource;
    if (this.isOptional) {
      if (this.isPointable) {
        nilCheck =
          "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
        nilCheck =
          "if %s == nil { return time.Time}".formatted(unAssertedDataSource);
      }
    }

    return """
    	func() %stime.Time {
    	var s string
    	%s
    	for i := dafny.Iterate(%s.(dafny.Sequence)); ; {
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
    		return %st
    	}
    }()""".formatted(
        this.isPointable ? "*" : "",
        nilCheck,
        dataSource,
        this.isPointable ? "&" : ""
      );
  }
}
