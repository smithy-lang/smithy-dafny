package software.amazon.polymorph.smithypython.localservice.shapevisitor;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * ShapeVisitor that should be dispatched from a Polymorph localService config shape
 * to generate code that maps a Smithy-modelled config shape's internal attributes
 * to the corresponding Dafny config shape's internal attributes.
 *
 * This largely defers to the SmithyToDafnyShapeVisitor implementation,
 * with the exception of StructureShapes.
 * This ShapeVisitor assumes all StructureShape members are required,
 *   since this is how Dafny code treats StructureShape members of localService
 *   config shapes.
 */
public class SmithyConfigToDafnyConfigShapeVisitor extends SmithyToDafnyShapeVisitor.Default<String> {
  private final GenerationContext context;
  private String dataSource;
  private final PythonWriter writer;
  private final String filename;

  /**
   * @param context The generation context.
   * @param dataSource The in-code location of the data to provide an output of
   *                   ({@code input.foo}, {@code entry}, etc.)
   */
  public SmithyConfigToDafnyConfigShapeVisitor(
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

  /**
   * Defers to SmithyToDafnyShapeVisitor by default.
   * @param shape Shape that is being visited.
   * @return
   */
  @Override
  protected String getDefault(Shape shape) {
    return shape.accept(
        new SmithyToDafnyShapeVisitor(context, dataSource, writer, filename)
    );
  }

  protected String getSmithyConfigToDafnyConfigFunctionNameForShape(Shape shape) {
    writer.addImport(".smithy_to_dafny", "SmithyToDafny_" + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(shape.getId().getNamespace())
        + "_" + shape.getId().getName());
    return "SmithyToDafny_" + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(shape.getId().getNamespace())
        + "_" + shape.getId().getName();
  }

  /**
   * Generates SmithyToDafny conversion logic for a Polymorph localService Config shape.
   * The provided StructureShape MUST be a Polymorph localService Config shape.
   * The primary
   * @param structureShape
   * @return
   */
  @Override
  public String structureShape(StructureShape structureShape) {
    // If this ShapeVisitor has not yet generated a conversion method for this shape,
    //   generate a conversion method
    if (!SmithyToDafnyShapeVisitor.generatedShapes.contains(structureShape)) {
      SmithyToDafnyShapeVisitor.generatedShapes.add(structureShape);
      writeStructureShapeConverter(structureShape);
    }

    // Import the smithy_to_dafny converter from where the ShapeVisitor was called
    writer.addImport(".smithy_to_dafny",
        SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape));

    // Return a reference to the generated conversion method
    // ex. for shape example.namespace.ExampleShape
    // returns `SmithyToDafny_example_namespace_ExampleShape(input)`
    return "%1$s(%2$s)".formatted(
        SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape),
        dataSource
    );
  }

  public void writeStructureShapeConverter(StructureShape shape) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", writerInstance -> {
      writerInstance.write(
          """
          def $L(input):
            return $L
          """,
          getSmithyConfigToDafnyConfigFunctionNameForShape(shape),
          getStructureShapeConverterBody(shape, writerInstance)
      );
    });
  }

  public String getStructureShapeConverterBody(StructureShape shape, PythonWriter writerInstance) {
    // Within the conversion function, the dataSource becomes the function's input
    // This hardcodes the input parameter name for a conversion function to always be "input"
    String dataSourceInsideConversionFunction = "input";

    if (!SmithyNameResolver.getLocalServiceConfigShapes(context).contains(shape.getId())) {
      throw new CodegenException(
          "Provided shape " + shape + " MUST be a localService config shape");
    }

    DafnyNameResolver.importDafnyTypeForShape(writerInstance, shape.getId(), context);
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

      // If this is (another!) localService config shape, defer conversion to the config ShapeVisitor
      if (SmithyNameResolver.getLocalServiceConfigShapes(context).contains(targetShape.getId())) {
        builder.append("%1$s,\n".formatted(
            targetShape.accept(
                new SmithyConfigToDafnyConfigShapeVisitor(
                    context,
                    dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName),
                    writer,
                    filename
                )
            )
        ));
      }
      // Otherwise, treat this member as required, and defer to standard shape visitor
      else {
        builder.append("%1$s,\n".formatted(
            targetShape.accept(
                new SmithyToDafnyShapeVisitor(
                    context,
                    dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName),
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
}
