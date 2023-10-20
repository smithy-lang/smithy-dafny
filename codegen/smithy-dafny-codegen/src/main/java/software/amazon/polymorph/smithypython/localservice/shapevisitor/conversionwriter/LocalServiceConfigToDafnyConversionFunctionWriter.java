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
 * Writes the shim.py file.
 * The shim wraps the client.py implementation (which itself wraps the underlying Dafny implementation).
 * Other Dafny-generated Python code may use the shim to interact with this project's Dafny implementation
 *   through the Polymorph wrapper.
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
    writer.addImport(".smithy_to_dafny", "SmithyToDafny_" + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(shape.getId().getNamespace())
        + "_" + shape.getId().getName());
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
                                  writer
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
                                  writer
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

  private void writeNonReferenceStructureShapeConverter(StructureShape shape, PythonWriter conversionWriter,
      String dataSourceInsideConversionFunction) {
    DafnyNameResolver.importDafnyTypeForShape(conversionWriter, shape.getId(), context);

    // Open Dafny structure shape
    // e.g.
    // DafnyStructureName(...
    conversionWriter.openBlock(
        "$L(",
        ")",
        DafnyNameResolver.getDafnyTypeForShape(shape),
        () -> {
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
            conversionWriter.writeInline("$L=", memberName);

            // If this is a localService config shape, defer conversion to the config ShapeVisitor
            if (SmithyNameResolver.getLocalServiceConfigShapes(context).contains(targetShape.getId())) {
              conversionWriter.write("$L,",
                  targetShape.accept(
                      new LocalServiceConfigToDafnyConfigShapeVisitor(
                          context,
                          dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName),
                          writer
                      )
                  )
              );
            }

            // If this shape is optional, write conversion logic to detect and possibly pass
            //   an empty optional at runtime
            else if (memberShape.isOptional()) {
              conversionWriter.addStdlibImport("Wrappers", "Option_Some");
              conversionWriter.addStdlibImport("Wrappers", "Option_None");
              conversionWriter.write(
                  "((Option_Some($L)) if ($L is not None) else (Option_None())),",
                  targetShape.accept(
                      new LocalServiceToDafnyShapeVisitor(
                          context,
                          dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName),
                          writer
                      )
                  ),
                  dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName)
              );
            }

            // If this shape is required, pass in the shape for conversion without any optional-checking
            else {
              conversionWriter.write("$L,",
                  targetShape.accept(
                      new LocalServiceToDafnyShapeVisitor(
                          context,
                          dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName),
                          writer
                      )
                  )
              );
            }
          }
        }
    );
  }
}