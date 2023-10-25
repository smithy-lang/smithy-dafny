package software.amazon.polymorph.smithypython.localservice.shapevisitor;

import java.util.Map.Entry;
import org.assertj.core.util.Strings;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter.LocalServiceConfigToDafnyConversionFunctionWriter;
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
public class LocalServiceConfigToDafnyConfigShapeVisitor extends LocalServiceToDafnyShapeVisitor.Default<String> {
  private final GenerationContext context;
  private final String dataSource;
  private final PythonWriter writer;
  private final String filename;
  /**
   * @param context The generation context.
   * @param dataSource The in-code location of the data to provide an output of
   *                   ({@code input.foo}, {@code entry}, etc.)
   */
  public LocalServiceConfigToDafnyConfigShapeVisitor(
      GenerationContext context,
      String dataSource,
      PythonWriter writer
  ) {
    this.context = context;
    this.dataSource = dataSource;
    this.writer = writer;
    this.filename = "";
  }

  public LocalServiceConfigToDafnyConfigShapeVisitor(
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
        new LocalServiceToDafnyShapeVisitor(context, dataSource, writer)
    );
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
    if (structureShape.getId().getNamespace().equals(context.settings().getService().getNamespace())) {

      LocalServiceConfigToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape,
        context, writer);
    }


//    // Import the smithy_to_dafny converter from where the ShapeVisitor was called
//    writer.addImport(".smithy_to_dafny",
//        SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape, context));

    String pythonModuleName = SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
        structureShape.getId().getNamespace(),
        context
    );
    System.out.println(pythonModuleName);
//    if (!structureShape.getId().getNamespace().equals(context.settings().getService().getNamespace()))  {
      writer.addStdlibImport(pythonModuleName + ".smithy_to_dafny");
//    }

    // Return a reference to the generated conversion method
    // ex. for shape example.namespace.ExampleShape
    // returns `SmithyToDafny_example_namespace_ExampleShape(input)`
    return "%1$s.smithy_to_dafny.%2$s(%3$s)".formatted(
        pythonModuleName,
        SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape, context),
        dataSource
    );
  }
}
