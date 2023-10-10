package software.amazon.polymorph.smithypython.shapevisitor;

import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.WriterDelegator;
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
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * ShapeVisitor that should be dispatched from a shape
 * to generate code that maps a Smithy-modelled shape's internal attributes
 * to the corresponding Dafny shape's internal attributes.
 */
public class SmithyToDafnyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private String dataSource;
    private final PythonWriter writer;
    private final String filename;
    static final Set<Shape> generatedShapes = new HashSet<>();

    /**
     * @param context The generation context.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code input.foo}, {@code entry}, etc.)
     */
    public SmithyToDafnyShapeVisitor(
        GenerationContext context,
        String dataSource,
        PythonWriter writer,
        String filename
    ) {
      this.context = context;
      this.dataSource = dataSource;
      this.writer = writer;
      this.filename = filename;
    }

    @Override
    protected String getDefault(Shape shape) {
      String protocolName = context.protocolGenerator().getName();
      throw new CodegenException(String.format(
          "Unsupported conversion of %s to %s using the %s protocol",
          shape, shape.getType(), protocolName));
    }

  protected String getSmithyToDafnyFunctionNameForShape(Shape shape) {
      writer.addImport(".smithy_to_dafny",  "SmithyToDafny_" + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(shape.getId().getNamespace())
          + "_" + shape.getId().getName());
    return "SmithyToDafny_" + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(shape.getId().getNamespace())
        + "_" + shape.getId().getName();
    }

    @Override
    public String blobShape(BlobShape shape) {
      return dataSource;
    }

    @Override
    public String structureShape(StructureShape shape) {
      String outStr = "%1$s(%2$s)".formatted(
          getSmithyToDafnyFunctionNameForShape(shape),
          dataSource
      );

      if (!generatedShapes.contains(shape)) {
        generatedShapes.add(shape);
        writeStructureShapeConverter(shape);
      }

      return outStr;
    }

  public void writeStructureShapeConverter(StructureShape shape) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    // TODO: Refactor
    this.dataSource = "input";

    delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", writerInstance -> {
      writerInstance.write(
          """
          def $L(input):
            return $L
          """,
          getSmithyToDafnyFunctionNameForShape(shape),
          getStructureShapeConverterBody(shape, writerInstance)
      );
    });
  }

  public String getStructureShapeConverterBody(StructureShape shape, PythonWriter writerInstance) {
    if (shape.hasTrait(ReferenceTrait.class)) {
      return referenceStructureShape(shape);
    }

    DafnyNameResolver.importDafnyTypeForShape(writerInstance, shape.getId());
    StringBuilder builder = new StringBuilder();
    // Open Dafny structure shape
    // e.g.
    // DafnyStructureName(...
    builder.append("%1$s(".formatted(DafnyNameResolver.getDafnyTypeForShape(shape)));
    // Recursively dispatch a new ShapeVisitor for each member of the structure
    for (Entry<String, MemberShape> memberShapeEntry : shape.getAllMembers().entrySet()) {
      String memberName = memberShapeEntry.getKey();
      MemberShape memberShape = memberShapeEntry.getValue();
      final Shape targetShape = context.model().expectShape(memberShape.getTarget());

      // Adds `DafnyStructureMember=smithy_structure_member(...)`
      // e.g.
      // DafnyStructureName(DafnyStructureMember=smithy_structure_member(...), ...)
      // The nature of the `smithy_structure_member` conversion depends on the properties of the shape,
      //   as described below
      builder.append("%1$s=".formatted(memberName));

      // If this is a localService config shape, defer conversion to the config ShapeVisitor
      if (SmithyNameResolver.getLocalServiceConfigShapes(context).contains(targetShape.getId())) {
        builder.append("%1$s,\n".formatted(
            targetShape.accept(
                new SmithyConfigToDafnyConfigShapeVisitor(
                    context,
                    dataSource + "." + CaseUtils.toSnakeCase(memberName),
                    writer,
                    filename
                )
            )
        ));
      }

      // If this shape is optional, write conversion logic to detect and possibly pass
      //   an empty optional at runtime
      else if (memberShape.isOptional()) {
        writerInstance.addStdlibImport("Wrappers", "Option_Some");
        writerInstance.addStdlibImport("Wrappers", "Option_None");
        builder.append(
            "((Option_Some(%1$s)) if (%2$s is not None) else (Option_None())),\n".formatted(
                targetShape.accept(
                    new SmithyToDafnyShapeVisitor(
                        context,
                        dataSource + "." + CaseUtils.toSnakeCase(memberName),
                        writer,
                        filename
                    )
                ),
                dataSource + "." + CaseUtils.toSnakeCase(memberName)
            ));
      }

      // If this shape is required, always unambiguously pass in the shape for conversion
      else {
        builder.append("%1$s,\n".formatted(
            targetShape.accept(
                new SmithyToDafnyShapeVisitor(
                    context,
                    dataSource + "." + CaseUtils.toSnakeCase(memberName),
                    writer,
                    filename
                )
            )
        ));
      }
    }
    // Close structure
    return builder.append(")").toString();
  }

    @Override
    public String listShape(ListShape shape) {
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();

      delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", writerInstance -> {
        writerInstance.addStdlibImport("_dafny", "Seq");
      });

      StringBuilder builder = new StringBuilder();

      // Open Dafny sequence:
      // `Seq([`
      builder.append("Seq([");
      MemberShape memberShape = shape.getMember();
      final Shape targetShape = context.model().expectShape(memberShape.getTarget());

      // Add converted list elements into the list:
      // `Seq([`SmithyToDafny(list_element)``
      builder.append("%1$s".formatted(
          targetShape.accept(
              new SmithyToDafnyShapeVisitor(context, "list_element", writer, filename)
          )));

      // Close structure
      // `Seq([`SmithyToDafny(list_element)` for list_element in `dataSource`])``
      return builder.append(" for list_element in %1$s])".formatted(dataSource)).toString();
    }

    @Override
    public String mapShape(MapShape shape) {
      StringBuilder builder = new StringBuilder();
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();

      delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", writerInstance -> {
        writerInstance.addStdlibImport("_dafny", "Map");
      });


      // Open Dafny map:
      // `Map({`
      builder.append("Map({");
      MemberShape keyMemberShape = shape.getKey();
      final Shape keyTargetShape = context.model().expectShape(keyMemberShape.getTarget());
      MemberShape valueMemberShape = shape.getValue();
      final Shape valueTargetShape = context.model().expectShape(valueMemberShape.getTarget());

      // Write converted map keys into the map:
      // `{`SmithyToDafny(key)`:`
      builder.append("%1$s: ".formatted(
          keyTargetShape.accept(
              new SmithyToDafnyShapeVisitor(context, "key", writer, filename)
          )
      ));

      // Write converted map values into the map:
      // `{`SmithyToDafny(key)`: `SmithyToDafny(value)``
      builder.append("%1$s".formatted(
          valueTargetShape.accept(
              new SmithyToDafnyShapeVisitor(context, "value", writer, filename)
          )
      ));

      // Complete map comprehension and close map
      // `{`SmithyToDafny(key)`: `SmithyToDafny(value)`` for (key, value) in `dataSource`.items() }`
      return builder.append(" for (key, value) in %1$s.items() })".formatted(dataSource)).toString();
    }

    @Override
    public String booleanShape(BooleanShape shape) {
      return dataSource;
    }

    @Override
    public String stringShape(StringShape shape) {
      return dataSource;
    }

    @Override
    public String byteShape(ByteShape shape) {
      return getDefault(shape);
    }

    @Override
    public String shortShape(ShortShape shape) {
      return getDefault(shape);
    }

    @Override
    public String integerShape(IntegerShape shape) {
      return dataSource;
    }

    @Override
    public String longShape(LongShape shape) {
      return dataSource;
    }

    @Override
    public String bigIntegerShape(BigIntegerShape shape) {
      return getDefault(shape);
    }

    @Override
    public String floatShape(FloatShape shape) {
      return getDefault(shape);
    }

    @Override
    public String doubleShape(DoubleShape shape) {
      return dataSource;
    }

    @Override
    public String bigDecimalShape(BigDecimalShape shape) {
      return getDefault(shape);
    }

    @Override
    public String enumShape(EnumShape shape) {
      return dataSource;
    }

    @Override
    public String timestampShape(TimestampShape shape) {
      return getDefault(shape);
    }

  public void writeUnionShapeConverter(UnionShape unionShape) {

    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    // TODO: Refactor
    this.dataSource = "input";

    delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", writerInstance -> {
      //writer.openBlock("class $L($T[Literal[$S]]):", "", symbol.getName(), apiError, code, () -> {
      writerInstance.openBlock(
          "def $L(input):", "", getSmithyToDafnyFunctionNameForShape(unionShape), () -> {

            // Union conversion cannot be done inline,
            // so PythonWriter writes a conversion block above the inline statement
            writerInstance.writeComment("Convert %1$s".formatted(
                unionShape.getId().getName()
            ));

            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            for (MemberShape memberShape : unionShape.getAllMembers().values()) {
              // Write out conversion:
              // if isinstance(my_union.member, union_type.possible_member):
              //     my_union_union_value = DafnyMyUnionPossibleMember(my_union.member.value)
              writerInstance.write("""
                      $L isinstance($L, $L):
                          $L_union_value = $L($L.$L)""",
                  // If we need a new `if` block, open one; otherwise, expand on existing one with `elif`
                  shouldOpenNewIfBlock ? "if" : "elif",
                  dataSource,
                  SmithyNameResolver.getSmithyGeneratedTypeForUnion(unionShape, memberShape),
                  unionShape.getId().getName(),
                  DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                  dataSource,
                  "value"
              );
              shouldOpenNewIfBlock = false;

              DafnyNameResolver.importDafnyTypeForUnion(writerInstance, unionShape, memberShape);
              SmithyNameResolver.importSmithyGeneratedTypeForUnion(writerInstance, context, unionShape,
                  memberShape);
            }

            // Handle no member in union.
            writerInstance.write("""
                    else:
                        raise Exception("No recognized union value in union type: " + $L)
                    """,
                dataSource
            );

            // Use the result of the union conversion inline
            writerInstance.write("return %1$s_union_value".formatted(unionShape.getId().getName()));
          });
    });
  }

  @Override
  public String unionShape(UnionShape unionShape) {
    String outStr = "%1$s(%2$s)".formatted(
        getSmithyToDafnyFunctionNameForShape(unionShape),
        dataSource
    );

    if (!generatedShapes.contains(unionShape)) {
      generatedShapes.add(unionShape);
      writeUnionShapeConverter(unionShape);
    }

    return outStr;

  }

  /**
   * Called from the StructureShape converter when the StructureShape has a Polymorph Reference trait.
   * @param shape
   * @return
   */
  protected String referenceStructureShape(StructureShape shape) {
    ReferenceTrait referenceTrait = shape.expectTrait(ReferenceTrait.class);
    Shape resourceOrService = context.model().expectShape(referenceTrait.getReferentId());

    if (resourceOrService.isResourceShape()) {
      return referenceResourceShape(resourceOrService.asResourceShape().get());
    } else if (resourceOrService.isServiceShape()) {
      return referenceServiceShape(resourceOrService.asServiceShape().get());
    } else {
      throw new UnsupportedOperationException("Unknown referenceStructureShape type: " + shape);
    }
  }

  protected String referenceServiceShape(ServiceShape serviceShape) {
    DafnyNameResolver.importDafnyTypeForServiceShape(writer, serviceShape);
    writer.addStdlibImport(SmithyNameResolver.getSmithyGeneratedConfigModulePathForSmithyNamespace(
        serviceShape.getId().getNamespace(), context));
    writer.addStdlibImport(DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(serviceShape));

    // `my_module_client = my_module_internaldafny.MyModuleClient()`
    writer.write("$L_client = $L.$L()",
        SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceShape.getId().getNamespace()),
        DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(serviceShape),
        DafnyNameResolver.getDafnyClientTypeForServiceShape(serviceShape)
    );
    // `my_module_client.ctor__(my_module.smithygenerated.config.smithy_config_to_dafny_config(input._config))`
    writer.write("$L_client.ctor__($L.smithy_config_to_dafny_config($L._config))",
        SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceShape.getId().getNamespace()),
        SmithyNameResolver.getSmithyGeneratedConfigModulePathForSmithyNamespace(
            serviceShape.getId().getNamespace(), context),
        dataSource
    );
    return "%1$s_client".formatted(SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(
        serviceShape.getId().getNamespace()));
  }

  protected String referenceResourceShape(ResourceShape resourceShape) {
    StringBuilder builder = new StringBuilder();


    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    return "input._impl";
//    delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", writerInstance -> {
//      DafnyNameResolver.importDafnyTypeForResourceShape(writer, resourceShape);
//
//      // Resource-specific imports
//      writerInstance.addStdlibImport(DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(resourceShape));
//      writerInstance.addStdlibImport(resourceShape.getId().getName(),
//          resourceShape.getId().getName(),
//          "Dafny" + resourceShape.getId().getName());
//
//      // `my_module_resource = DafnyMyModuleResource()`
//      builder.append("%1$s_resource = %2$s._impl\n".formatted(
//          SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(resourceShape.getId().getNamespace()),
//          dataSource
//      ));
//    });
//
//
//    // TODO: Inline the above conversion...??
//    // Use result of resource conversion inline
//    builder.append("%1$s_resource".formatted(SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(
//        resourceShape.getId().getNamespace())));
//    return builder.toString();
  }
}
