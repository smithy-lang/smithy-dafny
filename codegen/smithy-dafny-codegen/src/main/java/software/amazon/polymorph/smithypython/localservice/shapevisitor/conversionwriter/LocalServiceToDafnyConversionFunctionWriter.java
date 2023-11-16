// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.conversionwriters.AwsSdkToDafnyConversionFunctionWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
import software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter.BaseConversionWriter;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceConfigToDafnyConfigShapeVisitor;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * Writes the smithy_to_dafny.py file via the BaseConversionWriter implementation
 */
public class LocalServiceToDafnyConversionFunctionWriter extends BaseConversionWriter {

  // Use a singleton to preserve generatedShapes through multiple invocations of this class
  static LocalServiceToDafnyConversionFunctionWriter singleton;

  protected LocalServiceToDafnyConversionFunctionWriter() {
  }

  // Instantiate singleton at class-load time
  static {
    singleton = new LocalServiceToDafnyConversionFunctionWriter();
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
    // Defer localService config to the localService config converter
    if (SmithyNameResolver.getLocalServiceConfigShapes(context).contains(structureShape.getId())) {
      LocalServiceConfigToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape,
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
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape, context),
          dataSourceInsideConversionFunction,
          () -> {
            if (Utils.isUnitShape(structureShape.getId())) {
              conversionWriter.write("return None");
            } else if (structureShape.hasTrait(ReferenceTrait.class)) {
              writeReferenceStructureShapeConverter(structureShape, conversionWriter, dataSourceInsideConversionFunction);
            } else if (structureShape.hasTrait(PositionalTrait.class)) {
              writePositionalStructureShapeConverter(structureShape, conversionWriter, dataSourceInsideConversionFunction);
            } else {
              writeNonReferenceStructureShapeConverter(structureShape, conversionWriter, dataSourceInsideConversionFunction);
            }
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
        "return $L(",
        ")",
        DafnyNameResolver.getDafnyTypeForShape(shape),
        () -> {
          // Recursively dispatch a new ShapeVisitor for each member of the structure
          for (Entry<String, MemberShape> memberShapeEntry : shape.getAllMembers().entrySet()) {
            String memberName = memberShapeEntry.getKey();
            MemberShape memberShape = memberShapeEntry.getValue();
            writeNonReferenceStructureShapeMemberConverter(conversionWriter,
                dataSourceInsideConversionFunction, memberName, memberShape);
          }
        }
    );
  }

  private void writeNonReferenceStructureShapeMemberConverter(PythonWriter conversionWriter,
      String dataSourceInsideConversionFunction, String memberName, MemberShape memberShape) {
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
                  // Pass the `conversionWriter` as our source writer;
                  // if we need to add imports, the imports will only be needed
                  // from the conversionwriter file
                  conversionWriter,
                  "smithy_to_dafny"
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
              ShapeVisitorResolver.getToDafnyShapeVisitorForShape(targetShape,
                  context,
                  dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName),
                  conversionWriter,
                  "smithy_to_dafny"
              )
          ),
          dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName)
      );
    }

    // If this shape is required, pass in the shape for conversion without any optional-checking
    else {
      conversionWriter.write("$L,",
          targetShape.accept(
              ShapeVisitorResolver.getToDafnyShapeVisitorForShape(targetShape,
                  context,
                  dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(memberName),
                  conversionWriter,
                  "smithy_to_dafny"
              )
          )
      );
    }
  }

  /**
   * Called from the StructureShape converter when the StructureShape has a Polymorph Positional trait.
   * @return
   */
  protected void writePositionalStructureShapeConverter(StructureShape structureShape, PythonWriter conversionWriter,
      String dataSourceInsideConversionFunction) {
    final MemberShape onlyMember = PositionalTrait.onlyMember(structureShape);
    final Shape targetShape = context.model().expectShape(onlyMember.getTarget());

    conversionWriter.write("return $L",
        targetShape.accept(
            ShapeVisitorResolver.getToDafnyShapeVisitorForShape(targetShape,
                context,
                dataSourceInsideConversionFunction + "." + CaseUtils.toSnakeCase(onlyMember.getMemberName()),
                conversionWriter,
                "smithy_to_dafny"
            )
        )
    );
  }

  /**
   * Called from the StructureShape converter when the StructureShape has a Polymorph Reference trait.
   * @param shape
   * @return
   */
  protected void writeReferenceStructureShapeConverter(StructureShape shape, PythonWriter conversionWriter,
      String dataSourceInsideConversionFunction) {
    ReferenceTrait referenceTrait = shape.expectTrait(ReferenceTrait.class);
    Shape resourceOrService = context.model().expectShape(referenceTrait.getReferentId());

    if (resourceOrService.isResourceShape()) {
      writeResourceShapeConverter(resourceOrService.asResourceShape().get(),
          conversionWriter, dataSourceInsideConversionFunction);
    } else if (resourceOrService.isServiceShape()) {
      writeServiceShapeConverter(resourceOrService.asServiceShape().get(), conversionWriter,
          dataSourceInsideConversionFunction);
    } else {
      throw new UnsupportedOperationException("Unknown reference type: " + shape);
    }
  }

  protected void writeServiceShapeConverter(ServiceShape serviceShape,
      PythonWriter conversionWriter, String dataSourceInsideConversionFunction) {

    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      DafnyNameResolver.importDafnyTypeForServiceShape(conversionWriter, serviceShape);

      // Import service inline to avoid circular dependency
      conversionWriter.write("import $L",
          SmithyNameResolver.getSmithyGeneratedConfigModulePathForSmithyNamespace(
              serviceShape.getId().getNamespace(), context)
      );

      conversionWriter.addStdlibImport(DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(serviceShape));

      // `my_module_client = my_module_internaldafny.MyModuleClient()`
      conversionWriter.write("$L_client = $L.$L()",
          SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceShape.getId().getNamespace()),
          DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(serviceShape),
          DafnyNameResolver.getDafnyClientTypeForServiceShape(serviceShape)
      );

      // `my_module_client.ctor__(my_module.smithygenerated.config.smithy_config_to_dafny_config(input._config))`
      conversionWriter.write("$L_client.ctor__($L.smithy_config_to_dafny_config($L._config))",
          SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceShape.getId().getNamespace()),
          SmithyNameResolver.getSmithyGeneratedConfigModulePathForSmithyNamespace(
              serviceShape.getId().getNamespace(), context),
          dataSourceInsideConversionFunction
      );

      conversionWriter.write("return $L_client",
          SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceShape.getId().getNamespace()));
    } else {
      DafnyNameResolver.importDafnyTypeForServiceShape(conversionWriter, serviceShape);

      conversionWriter.write("""
          import $L
          client = $L.default__.$L()
          client.impl = input
          return client
          """,
          DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(serviceShape),
          DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(serviceShape),
          // TODO-Python: No
          serviceShape.getId().getName().equals("TrentService")
          ? "KMSClient"
              : "DynamoDBClient"
          );
    }

  }

  protected void writeResourceShapeConverter(ResourceShape resourceShape,
      PythonWriter conversionWriter, String dataSourceInsideConversionFunction) {
    // Smithy resource shapes ALWAYS store the underlying Dafny resource in `_impl`.
    // TODO-Python: Typing
    conversionWriter.write("return $L._impl",
        dataSourceInsideConversionFunction);
  }

  /**
   * Writes a function definition to convert a Smithy-modelled union shape
   *   into the corresponding Dafny-modelled union shape.
   * The function definition is written into `smithy_to_dafny.py`.
   * This SHOULD only be called once so only one function definition is written.
   * @param unionShape
   */
  public void writeUnionShapeConverter(UnionShape unionShape) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", conversionWriter -> {

      // Within the conversion function, the dataSource becomes the function's input
      // This hardcodes the input parameter name for a conversion function to always be "input"
      String dataSourceInsideConversionFunction = "input";

      // ex. shape: simple.union.ExampleUnion
      // Writes `def SmithyToDafny_simple_union_ExampleUnion(input):`
      //   and wraps inner code inside function definition
      conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(unionShape, context),
          dataSourceInsideConversionFunction,
          () -> {

            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            for (MemberShape memberShape : unionShape.getAllMembers().values()) {
              // Write out conversion:
              // ex. if ExampleUnion can take on either of (IntegerValue, StringValue), write:
              // if isinstance(input, ExampleUnion.IntegerValue):
              //   example_union_union_value = DafnyExampleUnionIntegerValue(input.member.value)
              // elif isinstance(input, ExampleUnion.StringValue):
              //   example_union_union_value = DafnyExampleUnionIntegerValue(input.member.value)
              conversionWriter.write("""
                        $L isinstance($L, $L.$L):
                            $L_union_value = $L($L.$L)""",
                  // If we need a new `if` block, open one; otherwise, expand on existing one with `elif`
                  shouldOpenNewIfBlock ? "if" : "elif",
                  dataSourceInsideConversionFunction,
                  SmithyNameResolver.getSmithyGeneratedModelLocationForShape(unionShape.getId(), context),
                  SmithyNameResolver.getSmithyGeneratedTypeForUnion(unionShape, memberShape),
                  unionShape.getId().getName(),
                  DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                  dataSourceInsideConversionFunction,
                  "value"
              );
              shouldOpenNewIfBlock = false;

              DafnyNameResolver.importDafnyTypeForUnion(conversionWriter, unionShape, memberShape);
              SmithyNameResolver.importSmithyGeneratedTypeForShape(conversionWriter, unionShape, context);
            }

            // Write case to handle if union member does not match any of the above cases
            conversionWriter.write("""
                      else:
                          raise ValueError("No recognized union value in union type: " + $L)
                      """,
                dataSourceInsideConversionFunction
            );

            // Return the result of the union conversion
            // `return example_union_union_value`
            conversionWriter.write("return %1$s_union_value".formatted(unionShape.getId().getName()));
          });
    });
  }

}