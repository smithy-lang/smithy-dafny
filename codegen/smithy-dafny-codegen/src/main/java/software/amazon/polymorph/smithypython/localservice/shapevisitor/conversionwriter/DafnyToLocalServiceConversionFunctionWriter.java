package software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
import software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter.BaseConversionWriter;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.DafnyToLocalServiceShapeVisitor;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceConfigToDafnyConfigShapeVisitor;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceToDafnyShapeVisitor;
import software.amazon.polymorph.traits.ReferenceTrait;
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
 * Writes the dafny_to_smithy.py file via the BaseConversionWriter implementation.
 */
public class DafnyToLocalServiceConversionFunctionWriter extends BaseConversionWriter {

  // Use a singleton to preserve generatedShapes through multiple invocations of this class
  static DafnyToLocalServiceConversionFunctionWriter singleton;

  protected DafnyToLocalServiceConversionFunctionWriter() {
  }

  // Instantiate singleton at class-load time
  static {
    singleton = new DafnyToLocalServiceConversionFunctionWriter();
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

  protected void writeStructureShapeConverter(StructureShape structureShape) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    delegator.useFileWriter(moduleName + "/dafny_to_smithy.py", "", conversionWriter -> {
      // Within the conversion function, the dataSource becomes the function's input
      // This hardcodes the input parameter name for a conversion function to always be "input"
      String dataSourceInsideConversionFunction = "input";

      conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(structureShape, context),
          Utils.isUnitShape(structureShape.getId()) ? "" : dataSourceInsideConversionFunction,
          () -> {
            if (structureShape.hasTrait(ReferenceTrait.class)) {
              writeReferenceStructureShapeConverter(structureShape, conversionWriter, dataSourceInsideConversionFunction);
            } else {
              writeNonReferenceStructureShapeConverter(structureShape, conversionWriter, dataSourceInsideConversionFunction);
            }
          }
      );
    });
  }

  private void writeNonReferenceStructureShapeConverter(StructureShape shape, PythonWriter conversionWriter,
      String dataSourceInsideConversionFunction) {
    SmithyNameResolver.importSmithyGeneratedTypeForShape(conversionWriter, shape, context);
    // Open Smithy structure shape
    // e.g.
    // smithy_structure_name(...
    conversionWriter.openBlock(
        "return $L(",
        ")",
        SmithyNameResolver.getSmithyGeneratedModelLocationForShape(
            shape.getId(), context
        ) + "." + shape.getId().getName(),
        () -> {
          // Recursively dispatch a new ShapeVisitor for each member of the structure
          for (Entry<String, MemberShape> memberShapeEntry : shape.getAllMembers().entrySet()) {
            String memberName = memberShapeEntry.getKey();
            MemberShape memberShape = memberShapeEntry.getValue();
            final Shape targetShape = context.model().expectShape(memberShape.getTarget());

            conversionWriter.writeInline("$L=", CaseUtils.toSnakeCase(memberName));

            if (memberShape.isOptional()) {
              conversionWriter.write("($L) if ($L.is_Some) else None,",
                targetShape.accept(
                    new DafnyToLocalServiceShapeVisitor(
                        context,
                        dataSourceInsideConversionFunction + "." + memberName + ".value",
                        conversionWriter,
                        "dafny_to_smithy"
                    )
                ),
                dataSourceInsideConversionFunction + "." + memberName
              );
            } else {
              // Adds `smithy_structure_member=DafnyStructureMember(...)`
              // e.g.
              // smithy_structure_name(smithy_structure_member=DafnyStructureMember(...), ...)
              conversionWriter.write("$L,",
                  targetShape.accept(
                      new DafnyToLocalServiceShapeVisitor(
                          context,
                          dataSourceInsideConversionFunction + "." + memberName,
                          conversionWriter,
                          "dafny_to_smithy"
                      )
                  )
              );
            }
          }
        }
    );
  }

  /**
   * Called from the StructureShape converter when the StructureShape has a Polymorph Reference trait.
   * @param structureShape
   * @return
   */
  private void writeReferenceStructureShapeConverter(StructureShape structureShape, PythonWriter conversionWriter,
      String dataSourceInsideConversionFunction) {
    ReferenceTrait referenceTrait = structureShape.expectTrait(ReferenceTrait.class);
    Shape resourceOrService = context.model().expectShape(referenceTrait.getReferentId());

    if (resourceOrService.isResourceShape()) {
      writeServiceShapeConverter(resourceOrService.asResourceShape().get(), conversionWriter,
          dataSourceInsideConversionFunction);
    } else if (resourceOrService.isServiceShape()) {
      writeResourceShapeConverter(resourceOrService.asServiceShape().get(), conversionWriter,
          dataSourceInsideConversionFunction);
    } else {
      throw new UnsupportedOperationException("Unknown referenceStructureShape type: " + structureShape);
    }
  }

  private void writeServiceShapeConverter(ResourceShape resourceShape, PythonWriter conversionWriter,
      String dataSourceInsideConversionFunction) {
//    conversionWriter.write()

        conversionWriter.write("from $L import $L",
            SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
                resourceShape.getId().getNamespace(), context
            ) + ".references",
            resourceShape.getId().getName()
            );

    conversionWriter.write("return $L(_impl=$L)",
        resourceShape.getId().getName(),
        dataSourceInsideConversionFunction);
  }

  private void writeResourceShapeConverter(ServiceShape serviceShape, PythonWriter conversionWriter,
      String dataSourceInsideConversionFunction) {
    conversionWriter.write("from $L import $L",
        SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
            serviceShape.getId().getNamespace(), context
        ) + ".client",
        serviceShape.getId().getName()
    );

    conversionWriter.write("return $L($L)",
        serviceShape.getId().getName(), dataSourceInsideConversionFunction);
  }

  /**
   * Writes a function definition to convert a Dafny-modelled union shape
   *   into the corresponding Smithy-modelled union shape.
   * The function definition is written into `dafny_to_smithy.py`.
   * This SHOULD only be called once so only one function definition is written.
   * @param unionShape
   */
  protected void writeUnionShapeConverter(UnionShape unionShape) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    // Write out common conversion function inside dafny_to_smithy
    delegator.useFileWriter(moduleName + "/dafny_to_smithy.py", "", conversionWriter -> {

      // Within the conversion function, the dataSource becomes the function's input
      String dataSourceInsideConversionFunction = "input";

      // ex. shape: simple.union.ExampleUnion
      // Writes `def DafnyToSmithy_simple_union_ExampleUnion(input):`
      //   and wraps inner code inside function definition
      conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(unionShape, context),
          dataSourceInsideConversionFunction,
          () -> {
            conversionWriter.writeComment("Convert %1$s".formatted(
                unionShape.getId().getName()
            ));

            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            // Write out conversion:
            // ex. if ExampleUnion can take on either of (IntegerValue, StringValue), write:
            // if isinstance(input, ExampleUnion_IntegerValue):
            //   ExampleUnion_union_value = ExampleUnionIntegerValue(input.IntegerValue)
            // elif isinstance(input, ExampleUnion_StringValue):
            //   ExampleUnion_union_value = ExampleUnionStringValue(input.StringValue)
            for (MemberShape memberShape : unionShape.getAllMembers().values()) {
              conversionWriter.write(
                  """
                  $L isinstance($L, $L):
                      $L_union_value = $L.$L($L.$L)""",
                  // If we need a new `if` block, open one; otherwise, expand on existing one with `elif`
                  shouldOpenNewIfBlock ? "if" : "elif",
                  dataSourceInsideConversionFunction,
                  DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                  unionShape.getId().getName(),
                  SmithyNameResolver.getSmithyGeneratedModelLocationForShape(unionShape.getId(), context),
                  SmithyNameResolver.getSmithyGeneratedTypeForUnion(unionShape, memberShape),
                  dataSourceInsideConversionFunction,
                  memberShape.getMemberName()
              );
              shouldOpenNewIfBlock = false;

              DafnyNameResolver.importDafnyTypeForUnion(conversionWriter, unionShape, memberShape);
              SmithyNameResolver.importSmithyGeneratedTypeForUnion(conversionWriter, context, unionShape, memberShape);
            }

            // Write case to handle if union member does not match any of the above cases
            conversionWriter.write("""
                  else:
                      raise ValueError("No recognized union value in union type: " + $L)
                  """,
                dataSourceInsideConversionFunction
            );

            // Write return value:
            // `return ExampleUnion_union_value`
            conversionWriter.write(
                """
                return $L_union_value
                """,
                unionShape.getId().getName()
            );
          }
      );
    });
  }

}