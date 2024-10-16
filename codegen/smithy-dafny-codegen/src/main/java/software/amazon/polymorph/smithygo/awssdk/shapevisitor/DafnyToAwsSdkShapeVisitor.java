package software.amazon.polymorph.smithygo.awssdk.shapevisitor;

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

// TODO: Remove anonymous function in each of the shape visitor and test if it will work
public class DafnyToAwsSdkShapeVisitor extends ShapeVisitor.Default<String> {

  private static final List<String> shapeName = Arrays.asList(
    "IndexSizeBytes",
    "ItemCount",
    "ProcessedSizeBytes",
    "TableSizeBytes"
  );
  private final AwsSdkGoPointableIndex awsSdkGoPointableIndex;
  private final GenerationContext context;
  private final String dataSource;
  private final GoWriter writer;
  private final ServiceTrait serviceTrait;
  private final boolean isOptional;
  private final boolean isPointable;

  //TODO: Ideally this shouldn't be static but with current design we need to access this across instances.
  private static final Map<MemberShape, String> memberShapeConversionFuncMap = new HashMap<>();

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
    final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
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
    final var builder = new StringBuilder();
    writer.addImportFromModule(
      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
        shape.toShapeId().getNamespace()
      ),
      DafnyNameResolver.dafnyTypesNamespace(shape)
    );
    final var subtype =
      !(awsSdkGoPointableIndex.isOperationStruct(shape) ||
        shape.hasTrait(Synthetic.class)) ||
      shape.toShapeId().getName().contains("Exception");
    var nilcheck = "";
    if (this.isOptional) {
      if (this.isPointable) {
        final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
        nilcheck = "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
        nilcheck = "";
      }
    }
    builder.append(
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
      final var assertionRequired =
        memberShape.isOptional();
      final var derivedDataSource =
        "%1$s%2$s%3$s%4$s".formatted(
            dataSource,
            maybeAssertion,
            ".Dtor_%s()".formatted(memberName),
            memberShape.isOptional() ? ".UnwrapOr(nil)" : ""
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
              memberShape.isOptional(),
              shapeName.contains(memberName) ||
              awsSdkGoPointableIndex.isPointable(targetShape)
            )
          )
      );
    }

    return builder.append("}}()").toString();
  }

  // TODO: smithy-dafny-conversion library
  @Override
  public String listShape(final ListShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    final StringBuilder builder = new StringBuilder();

    final MemberShape memberShape = shape.getMember();
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());
    final var typeName = GoCodegenUtils.getType(
      context.symbolProvider().toSymbol(targetShape),
      serviceTrait
    );
    final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
    builder.append(
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
    return builder.append("return fieldValue }()").toString();
  }

  @Override
  public String mapShape(final MapShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    final StringBuilder builder = new StringBuilder();

    final MemberShape keyMemberShape = shape.getKey();
    final MemberShape valueMemberShape = shape.getValue();
    final Shape valueTargetShape = context
      .model()
      .expectShape(valueMemberShape.getTarget());
      final var typeName = GoCodegenUtils.getType(
      context.symbolProvider().toSymbol(valueTargetShape),
      serviceTrait
    );

    var nilCheck = "";
    final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
    if (this.isOptional) {
      nilCheck =
        """
        if %s == nil {
            return nil
        }
        """.formatted(unAssertedDataSource);
    }
    builder.append(
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
    return builder.toString();
  }

  @Override
  public String booleanShape(final BooleanShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    var nilCheck = "";
    final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
    if (this.isOptional) {
      if (this.isPointable) {
        nilCheck = "if %s == nil { return nil }".formatted(unAssertedDataSource);
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
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    if (shape.hasTrait(EnumTrait.class)) {
      if (this.isOptional) {
        final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
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
        }()""".formatted(
            SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, true),
            context.symbolProvider().toSymbol(shape).getName(),
            SmithyNameResolver.smithyTypesNamespaceAws(serviceTrait, true),
            context.symbolProvider().toSymbol(shape).getName(),
            unAssertedDataSource,
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
           func () %s.%s {
           var u %s.%s

        	inputEnum := %s
        	index := -1;
        	for allEnums := dafny.Iterate(%s{}.AllSingletonConstructors()); ; {
        		enum, ok := allEnums()
        		if ok {
        			index++
        			if enum.(%s).Equals(inputEnum.(%s)) {
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
            dataSource,
            DafnyNameResolver.getDafnyCompanionStructType(
              shape,
              context.symbolProvider().toSymbol(shape)
            ),
            DafnyNameResolver.getDafnyType(
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

    final var underlyingType = shape.hasTrait(DafnyUtf8BytesTrait.class)
      ? "uint8"
      : "dafny.Char";
    var nilCheck = "";
    final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
    if (this.isOptional) {
      if (this.isPointable) {
        nilCheck = "if %s == nil { return nil }".formatted(unAssertedDataSource);
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
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    if (AwsSdkGoPointableIndex.of(context.model()).isPointable(shape)) {
      final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
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
      return "%s".formatted(
          dataSource
        );
    }
  }

  @Override
  public String longShape(final LongShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    var nilCheck = "";
    final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
    if (this.isOptional) {
      if (this.isPointable) {
        nilCheck = "if %s == nil { return nil }".formatted(unAssertedDataSource);
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
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    writer.addUseImports(SmithyGoDependency.MATH);
    writer.addUseImports(SmithyGoDependency.stdlib("encoding/binary"));
    var nilCheck = "";
    if (this.isOptional) {
      final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
      if (this.isPointable) {
        nilCheck = "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
        nilCheck =
          "if %s == nil { var f float64; return f}".formatted(unAssertedDataSource);
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
    writer.addImportFromModule("github.com/dafny-lang/DafnyStandardLibGo", "Wrappers");
    var nilCheck = "";
    if (this.isOptional) {
      final String unAssertedDataSource = dataSource.startsWith("input.(") ? "input" : dataSource;
      if (this.isPointable) {
          nilCheck = "if %s == nil { return nil }".formatted(unAssertedDataSource);
      } else {
          nilCheck = "if %s == nil { return union}".formatted(unAssertedDataSource);
      }
    }
    final var functionInit = """
        func() %s {
            var union %s
            %s
        """.formatted(
            SmithyNameResolver.getSmithyTypeAws(serviceTrait, context.symbolProvider().toSymbol(shape), true),
            SmithyNameResolver.getSmithyTypeAws(serviceTrait, context.symbolProvider().toSymbol(shape), true),
            nilCheck
    );
    final var eachMemberInUnion = new StringBuilder();
    for (final var member : shape.getAllMembers().values()) {
        final var targetShape = context.model().expectShape(member.getTarget());
        final var memberName = context.symbolProvider().toMemberName(member);
        // unwrap union type, assert it then convert it to its member type with Dtor_ (example: Dtor_BlobValue()). unionDataSource is not a wrapper object until now.
        var unionDataSource = dataSource.concat(".Dtor_").concat(memberName.replace(shape.getId().getName().concat("Member"), "")).concat("()");
        final var isMemberShapePointable = (awsSdkGoPointableIndex.isPointable(targetShape) && awsSdkGoPointableIndex.isDereferencable(targetShape)) && !targetShape.isStructureShape();
        final var pointerForPointableShape = isMemberShapePointable ? "*" : "";
        final var isMemberCheck = """
                    if ((%s).%s()) {""".formatted(
                dataSource,
                memberName.replace(shape.getId().getName().concat("Member"), "Is_")
        );
        var wrappedDataSource = "";
        var requiresAssertion = true;
        if (!(targetShape.isStructureShape())) {
            // All other shape except structure needs a Wrapper object but unionDataSource is not a Wrapper object.
            wrappedDataSource = """
                var dataSource = Wrappers.Companion_Option_.Create_Some_(%s)""".formatted(unionDataSource);
            unionDataSource = "dataSource.UnwrapOr(nil)";
            requiresAssertion = false;
        }
        eachMemberInUnion.append("""
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
                  isMemberShapePointable)
                )
              );
    }
    return
            """
                %s
                %s
                return union
            }()""".formatted(
                    functionInit,
                    eachMemberInUnion
            );
  }

  @Override
  public String timestampShape(final TimestampShape shape) {
    // TODO: Figure out timestamp types when working on timestampShape 
    writer.addImport("time");
    return "nil";
  }
}
