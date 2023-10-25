package software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter.BaseConversionWriter;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceConfigToDafnyConfigShapeVisitor;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceToDafnyShapeVisitor;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * Writes the smithy_to_dafny.py file via the BaseConversionWriter implementation
 *   ONLY for localService config shapes.
 */
public class LocalServiceConfigToDafnyConversionFunctionWriter extends LocalServiceToDafnyConversionFunctionWriter {

  // Use a singleton to preserve generatedShapes through multiple invocations of this class
  static LocalServiceConfigToDafnyConversionFunctionWriter singleton;

  private LocalServiceConfigToDafnyConversionFunctionWriter() {
    super();
  }

  // Instantiate singleton at class-load time
  static {
    singleton = new LocalServiceConfigToDafnyConversionFunctionWriter();
  }

  /**
   * Delegate writing conversion methods for the provided shape and its member shapes
   *
   * @param shape
   * @param context
   * @param writer
   */
  public static void writeConverterForShapeAndMembers(Shape shape, GenerationContext context,
      PythonWriter writer) {
    singleton.baseWriteConverterForShapeAndMembers(shape, context, writer);
  }

  protected String getSmithyConfigToDafnyConfigFunctionNameForShape(Shape shape) {
    return "SmithyToDafny_" + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(shape.getId().getNamespace())
        + "_" + shape.getId().getName();
  }

  protected void writeStructureShapeConverter(StructureShape structureShape) {
    // Defer non-localService config shapes to the non-localService config shape converter
    if (!SmithyNameResolver.getLocalServiceConfigShapes(context).contains(structureShape.getId())) {
      LocalServiceToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape,
          context, writer);
      return;
    }

    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", conversionWriter -> {
      // Within the conversion function, the dataSource becomes the function's input
      // This hardcodes the input parameter name for a conversion function to always be "input"
      String dataSourceInsideConversionFunction = "input";

      conversionWriter.openBlock(
          "def $L($L):",
          "",
          getSmithyConfigToDafnyConfigFunctionNameForShape(structureShape),
          dataSourceInsideConversionFunction,
          () -> {
            DafnyNameResolver.importDafnyTypeForShape(conversionWriter, structureShape.getId(), context);
            StringBuilder builder = new StringBuilder();
            // Open Dafny structure shape
            // e.g.
            // DafnyStructureName(...
            conversionWriter.openBlock(
                "return $L(",
                ")",
                DafnyNameResolver.getDafnyTypeForShape(structureShape),
                () -> {
                  // Recursively dispatch a new ShapeVisitor for each member of the structure
                  for (Entry<String, MemberShape> memberShapeEntry : structureShape.getAllMembers().entrySet()) {
                    String memberName = memberShapeEntry.getKey();
                    MemberShape memberShape = memberShapeEntry.getValue();
                    final Shape targetShape = context.model().expectShape(memberShape.getTarget());

                    // Adds `DafnyStructureMember=smithy_structure_member(...)`
                    // e.g.
                    // DafnyStructureName(DafnyStructureMember=smithy_structure_member(...), ...)
                    // The nature of the `smithy_structure_member` conversion depends on the properties of the shape,
                    //   as described below
                    conversionWriter.writeInline("$L=", memberName);

                    // If this is (another!) localService config shape, defer conversion to the config ShapeVisitor
                    if (SmithyNameResolver.getLocalServiceConfigShapes(context).contains(targetShape.getId())) {
                      conversionWriter.write("$L,",
                          targetShape.accept(
                              new LocalServiceConfigToDafnyConfigShapeVisitor(
                                  context,
                                  dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName),
                                  conversionWriter,
                                  "smithy_to_dafny"
                              )
                          )
                      );
                    }
                    // Otherwise, treat this member as required,
                    // even though the Smithy model marks it as optional,
                    // and defer to standard shape visitor
                    else {
                      conversionWriter.write("$L,",
                          targetShape.accept(
                              new LocalServiceToDafnyShapeVisitor(
                                  context,
                                  dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName),
                                  conversionWriter,
                                  "smithy_to_dafny"
                              )
                          )
                      );
                    }
                  }
                }
            );
          }
      );
    });
  }
}