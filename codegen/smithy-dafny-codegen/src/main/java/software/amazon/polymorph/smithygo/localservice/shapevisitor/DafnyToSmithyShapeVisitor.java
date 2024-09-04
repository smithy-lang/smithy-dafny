package software.amazon.polymorph.smithygo.localservice.shapevisitor;

import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.codegen.knowledge.GoPointableIndex;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
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
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.utils.StringUtils;

public class DafnyToSmithyShapeVisitor extends ShapeVisitor.Default<String> {

  private final GenerationContext context;
  private final String dataSource;
  private final GoWriter writer;
  private final boolean isConfigShape;
  private final boolean isOptional;

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

  protected String referenceStructureShape(StructureShape shape) {
    ReferenceTrait referenceTrait = shape.expectTrait(ReferenceTrait.class);
    Shape resourceOrService = context
      .model()
      .expectShape(referenceTrait.getReferentId());
    var namespace = "";
    if (resourceOrService.asResourceShape().isPresent()) {
      var resourceShape = resourceOrService.asResourceShape().get();
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
      var serviceShape = resourceOrService.asServiceShape().get();
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
        return "%1$s{%2$s}".formatted(
            namespace.concat(
              context.symbolProvider().toSymbol(serviceShape).getName()
            ),
            dataSource
          );
      }
      return """
      func () *%s {
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
          DafnyNameResolver.getDafnyClient(
            serviceShape,
            serviceShape.toShapeId().getName()
          )
        );
    }
  }

  @Override
  protected String getDefault(Shape shape) {
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

    builder.append(
      "%1$s{".formatted(
          SmithyNameResolver
            .smithyTypesNamespace(shape)
            .concat(".")
            .concat(shape.getId().getName())
        )
    );
    String fieldSeparator = ",";
    for (final var memberShapeEntry : shape.getAllMembers().entrySet()) {
      final var memberName = memberShapeEntry.getKey();
      final var memberShape = memberShapeEntry.getValue();
      final var targetShape = context
        .model()
        .expectShape(memberShape.getTarget());
      //TODO: Is it ever possible for structure to be nil?
      final var derivedDataSource =
        "%1$s%2$s%3$s%4$s".formatted(
            dataSource,
            ".Dtor_%s()".formatted(memberName),
            memberShape.isOptional() ? ".UnwrapOr(nil)" : "",
            memberShape.isOptional() &&
              targetShape.isStructureShape() &&
              !targetShape.hasTrait(ReferenceTrait.class)
              ? ".(%s)".formatted(
                  DafnyNameResolver.getDafnyType(
                    targetShape,
                    context.symbolProvider().toSymbol(memberShape)
                  )
                )
              : ""
          );
      builder.append(
        "%1$s: %2$s%3$s,".formatted(
            StringUtils.capitalize(memberName),
            (targetShape.isStructureShape() && memberShape.isOptional()) &&
              !targetShape.hasTrait(ReferenceTrait.class)
              ? "&"
              : "",
            targetShape.accept(
              new DafnyToSmithyShapeVisitor(
                context,
                derivedDataSource,
                writer,
                isConfigShape,
                memberShape.isOptional()
              )
            )
          )
      );
    }

    return builder.append("}").toString();
  }

  // TODO: smithy-dafny-conversion library
  @Override
  public String listShape(ListShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    StringBuilder builder = new StringBuilder();

    MemberShape memberShape = shape.getMember();
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());
    var typeName = targetShape.isStructureShape()
      ? context.symbolProvider().toSymbol(memberShape)
      : context.symbolProvider().toSymbol(memberShape);
    builder.append(
      """
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
      	fieldValue = append(fieldValue, %s)}
      	""".formatted(
          SmithyNameResolver.getSmithyType(shape, typeName),
          SmithyNameResolver.getSmithyType(shape, typeName),
          dataSource,
          dataSource,
          targetShape.accept(
            new DafnyToSmithyShapeVisitor(
              context,
              "val%s".formatted(
                  targetShape.isStructureShape()
                    ? ".(%s)".formatted(
                        DafnyNameResolver.getDafnyType(
                          targetShape,
                          context.symbolProvider().toSymbol(targetShape)
                        )
                      )
                    : ""
                ),
              writer,
              isConfigShape
            )
          )
        )
    );

    // Close structure
    return builder
      .append("return fieldValue }()".formatted(dataSource))
      .toString();
  }

  @Override
  public String mapShape(MapShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    StringBuilder builder = new StringBuilder();

    MemberShape keyMemberShape = shape.getKey();
    final Shape keyTargetShape = context
      .model()
      .expectShape(keyMemberShape.getTarget());
    MemberShape valueMemberShape = shape.getValue();
    final Shape valueTargetShape = context
      .model()
      .expectShape(valueMemberShape.getTarget());
    final var type = context
      .symbolProvider()
      .toSymbol(valueTargetShape)
      .getName();

    builder.append(
      """
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
      	m[%s] = %s
      }
      return m
                                    }()""".formatted(
          type,
          type,
          type,
          dataSource,
          dataSource,
          keyTargetShape.accept(
            new DafnyToSmithyShapeVisitor(
              context,
              "(*val.(dafny.Tuple).IndexInt(0))",
              writer,
              isConfigShape
            )
          ),
          valueTargetShape.accept(
            new DafnyToSmithyShapeVisitor(
              context,
              "(*val.(dafny.Tuple).IndexInt(1))",
              writer,
              isConfigShape
            )
          )
        )
    );
    return builder.toString();
  }

  @Override
  public String booleanShape(BooleanShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    if (this.isOptional) {
      return """
      func() *bool {
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
      return "%s.(%s)".formatted(
          dataSource,
          context.symbolProvider().toSymbol(shape).getName()
        );
    }
  }

  @Override
  public String stringShape(StringShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    if (shape.hasTrait(EnumTrait.class)) {
      return """
         func () *%s.%s {
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

    var underlyingType = shape.hasTrait(DafnyUtf8BytesTrait.class)
      ? "uint8"
      : "dafny.Char";
    var strConv = "s = s + string(val.(%s))".formatted(underlyingType);
    if (underlyingType == "uint8") {
      strConv =
        """
            // UTF bytes should be always converted from bytes to string in go
            // Otherwise go treats the string as a unicode codepoint

            var valUint, _ = val.(%s)
            var byteSlice = []byte{valUint}
            s = s + string(byteSlice)
        """.formatted(underlyingType);
    }
    if ((boolean) isOptional) {
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
                   %s
               }
          }
      }()""".formatted(dataSource, dataSource, strConv);
    } else {
      return """
       func() (string) {
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
  public String integerShape(IntegerShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");

    if ((boolean) isOptional) {
      return (
        """
        func() *int32 {
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
      func() int32 {
          var b = %s.(int32)
          return b
      }()
          """.formatted(dataSource);
    }
  }

  @Override
  public String longShape(LongShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    return (
      """
      func() *int64 {
          var b int64
          if %s == nil {
              return nil
          }
          b = %s.(int64)
          return &b
      }()"""
    ).formatted(dataSource, dataSource);
  }

  @Override
  public String doubleShape(DoubleShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    writer.addUseImports(SmithyGoDependency.MATH);
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

  @Override
  public String unionShape(UnionShape shape) {
    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
    String nilCheck;
    if (GoPointableIndex.of(context.model()).isPointable(shape) == false) {
      nilCheck = "";
    } else {
      nilCheck =
        """
        if %s == nil {
                return nil
        }""".formatted(dataSource);
    }
    final String functionInit =
      """
      func() %s {
          var union %s
          %s
      """.formatted(
          context.symbolProvider().toSymbol(shape),
          context.symbolProvider().toSymbol(shape),
          nilCheck
        );
    StringBuilder eachMemberInUnion = new StringBuilder();
    for (var member : shape.getAllMembers().values()) {
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
        memberName.replace(shape.getId().getName() + "Member", "") +
        "()";
      final Boolean isMemberShapePointable =
        (GoPointableIndex.of(context.model()).isPointable(targetShape) &&
          GoPointableIndex.of(context.model()).isDereferencable(targetShape)) &&
        !targetShape.isStructureShape();
      final String pointerForPointableShape = isMemberShapePointable ? "*" : "";
      final String isMemberCheck =
        """
        if ((%s).%s()) {""".formatted(
            rawUnionDataSource,
            memberName.replace(shape.getId().getName() + "Member", "Is_")
          );
      String wrappedDataSource = "";
      if (!(targetShape.isStructureShape())) {
        // All other shape except structure needs a Wrapper object but unionDataSource is not a Wrapper object.
        wrappedDataSource =
          """
          var dataSource = Wrappers.Companion_Option_.Create_Some_(%s)""".formatted(
              unionDataSource
            );
        unionDataSource = "dataSource.UnwrapOr(nil)";
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
            targetShape.accept(
              new DafnyToSmithyShapeVisitor(
                context,
                unionDataSource,
                writer,
                isConfigShape,
                isMemberShapePointable
              )
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
  public String timestampShape(TimestampShape shape) {
    return "nil";
  }
}
