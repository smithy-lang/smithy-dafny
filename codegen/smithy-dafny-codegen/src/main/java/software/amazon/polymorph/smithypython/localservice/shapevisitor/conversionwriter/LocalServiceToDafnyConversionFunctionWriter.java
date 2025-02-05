// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter.BaseConversionWriter;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceToDafnyShapeVisitor;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/** Writes the smithy_to_dafny.py file via the BaseConversionWriter implementation */
public class LocalServiceToDafnyConversionFunctionWriter
  extends BaseConversionWriter {

  // Use a singleton to preserve generatedShapes through multiple invocations of this class
  static LocalServiceToDafnyConversionFunctionWriter singleton;

  protected LocalServiceToDafnyConversionFunctionWriter() {}

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
  public static void writeConverterForShapeAndMembers(
    Shape shape,
    GenerationContext context,
    PythonWriter writer
  ) {
    singleton.baseWriteConverterForShapeAndMembers(shape, context, writer);
  }

  @Override
  protected void writeStructureShapeConverter(StructureShape structureShape) {
    final WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    final String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    delegator.useFileWriter(
      moduleName + "/smithy_to_dafny.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        // This hardcodes the input parameter name for a conversion function to always be
        // "native_input"
        String dataSourceInsideConversionFunction = "native_input";

        conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(
            structureShape,
            context
          ),
          dataSourceInsideConversionFunction,
          () -> {
            if (SmithyNameResolver.isUnitShape(structureShape.getId())) {
              conversionWriter.write("return None");
            } else if (structureShape.hasTrait(ReferenceTrait.class)) {
              writeReferenceStructureShapeConverter(
                structureShape,
                conversionWriter,
                dataSourceInsideConversionFunction
              );
            } else if (structureShape.hasTrait(PositionalTrait.class)) {
              writePositionalStructureShapeConverter(
                structureShape,
                conversionWriter,
                dataSourceInsideConversionFunction
              );
            } else {
              writeNonReferenceStructureShapeConverter(
                structureShape,
                conversionWriter,
                dataSourceInsideConversionFunction
              );
            }
          }
        );
      }
    );
  }

  private void writeNonReferenceStructureShapeConverter(
    StructureShape shape,
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction
  ) {
    DafnyNameResolver.importDafnyTypeForShape(
      conversionWriter,
      shape.getId(),
      context
    );

    // Open Dafny structure shape
    // e.g.
    // DafnyStructureName(...
    conversionWriter.openBlock(
      "return $L(",
      ")",
      DafnyNameResolver.getDafnyTypeForShape(shape),
      () -> {
        // Recursively dispatch a new ShapeVisitor for each member of the structure
        for (Entry<String, MemberShape> memberShapeEntry : shape
          .getAllMembers()
          .entrySet()) {
          String memberName = memberShapeEntry.getKey();
          MemberShape memberShape = memberShapeEntry.getValue();
          writeNonReferenceStructureShapeMemberConverter(
            conversionWriter,
            dataSourceInsideConversionFunction,
            memberName,
            memberShape
          );
        }
      }
    );
  }

  private void writeNonReferenceStructureShapeMemberConverter(
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction,
    String memberName,
    MemberShape memberShape
  ) {
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());

    // Adds `DafnyStructureMember=smithy_structure_member(...)`
    // e.g.
    // DafnyStructureName(DafnyStructureMember=smithy_structure_member(...), ...)
    // The nature of the `smithy_structure_member` conversion depends on the properties of the
    // shape,
    //   as described below
    conversionWriter.writeInline("$L=", memberName);

    if (
      context
        .model()
        .expectShape(memberShape.getTarget())
        .hasTrait(ReferenceTrait.class)
    ) {
      if (memberShape.isOptional()) {
        conversionWriter.write(
          "((Option_Some($2L)) if (($1L is not None) and ($2L is not None)) else (Option_None())),",
          dataSourceInsideConversionFunction +
          "." +
          CaseUtils.toSnakeCase(memberName),
          targetShape.accept(
            ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
              targetShape,
              context,
              dataSourceInsideConversionFunction +
              "." +
              CaseUtils.toSnakeCase(memberName),
              conversionWriter,
              "smithy_to_dafny"
            )
          )
        );
      } else {
        conversionWriter.write(
          "$L,",
          targetShape.accept(
            ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
              targetShape,
              context,
              dataSourceInsideConversionFunction +
              "." +
              CaseUtils.toSnakeCase(memberName),
              conversionWriter,
              "smithy_to_dafny"
            )
          )
        );
      }
    }
    // If this shape is optional, write conversion logic to detect and possibly pass
    //   an empty optional at runtime
    else if (memberShape.isOptional()) {
      conversionWriter.addStdlibImport(
        "smithy_dafny_standard_library.internaldafny.generated.Wrappers",
        "Option_Some"
      );
      conversionWriter.addStdlibImport(
        "smithy_dafny_standard_library.internaldafny.generated.Wrappers",
        "Option_None"
      );
      conversionWriter.write(
        "((Option_Some($L)) if ($L is not None) else (Option_None())),",
        targetShape.accept(
          ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
            targetShape,
            context,
            dataSourceInsideConversionFunction +
            "." +
            CaseUtils.toSnakeCase(memberName),
            conversionWriter,
            "smithy_to_dafny"
          )
        ),
        dataSourceInsideConversionFunction +
        "." +
        CaseUtils.toSnakeCase(memberName)
      );
    }
    // If this shape is required, pass in the shape for conversion without any optional-checking
    else {
      conversionWriter.write(
        "$L,",
        targetShape.accept(
          ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
            targetShape,
            context,
            dataSourceInsideConversionFunction +
            "." +
            CaseUtils.toSnakeCase(memberName),
            conversionWriter,
            "smithy_to_dafny"
          )
        )
      );
    }
  }

  /**
   * Called from the StructureShape converter when the StructureShape has a Polymorph Positional
   * trait.
   *
   * @return
   */
  protected void writePositionalStructureShapeConverter(
    StructureShape structureShape,
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction
  ) {
    final MemberShape onlyMember = PositionalTrait.onlyMember(structureShape);
    final Shape targetShape = context
      .model()
      .expectShape(onlyMember.getTarget());

    conversionWriter.write(
      "return $L",
      targetShape.accept(
        ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
          targetShape,
          context,
          dataSourceInsideConversionFunction,
          conversionWriter,
          "smithy_to_dafny"
        )
      )
    );
  }

  /**
   * Called from the StructureShape converter when the StructureShape has a Polymorph Reference
   * trait.
   *
   * @param shape
   * @return
   */
  protected void writeReferenceStructureShapeConverter(
    StructureShape shape,
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction
  ) {
    final ReferenceTrait referenceTrait = shape.expectTrait(
      ReferenceTrait.class
    );
    final Shape resourceOrService = context
      .model()
      .expectShape(referenceTrait.getReferentId());

    if (resourceOrService.isResourceShape()) {
      writeResourceShapeConverter(
        resourceOrService.asResourceShape().get(),
        conversionWriter,
        dataSourceInsideConversionFunction
      );
    } else if (resourceOrService.isServiceShape()) {
      writeServiceShapeConverter(
        resourceOrService.asServiceShape().get(),
        conversionWriter,
        dataSourceInsideConversionFunction
      );
    } else {
      throw new UnsupportedOperationException(
        "Unknown reference type: " + shape
      );
    }
  }

  protected void writeServiceShapeConverter(
    ServiceShape serviceShape,
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction
  ) {
    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      conversionWriter.write(
        "return $L._config.dafnyImplInterface.impl",
        dataSourceInsideConversionFunction
      );
    } else {
      DafnyNameResolver.importDafnyTypeForServiceShape(
        conversionWriter,
        serviceShape,
        context
      );

      conversionWriter.write(
        """
        import $1L
        client = $1L.default__.$2L(boto_client = $3L)
        client.value.impl = $3L
        return client.value
        """,
        DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(
          serviceShape,
          context
        ),
        AwsSdkNameResolver.clientNameForService(serviceShape),
        dataSourceInsideConversionFunction
      );
    }
  }

  protected void writeResourceShapeConverter(
    ResourceShape resourceShape,
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction
  ) {
    conversionWriter.openBlock(
      "if hasattr($L, '_impl'):",
      "",
      dataSourceInsideConversionFunction,
      () -> {
        conversionWriter.write(
          "return $L._impl",
          dataSourceInsideConversionFunction
        );
      }
    );

    conversionWriter.openBlock(
      "else:",
      "",
      () -> {
        conversionWriter.write("return $L", dataSourceInsideConversionFunction);
      }
    );
  }

  /**
   * Writes a function definition to convert a Smithy-modelled union shape into the corresponding
   * Dafny-modelled union shape. The function definition is written into `smithy_to_dafny.py`. This
   * SHOULD only be called once so only one function definition is written.
   *
   * @param unionShape
   */
  @Override
  protected void writeUnionShapeConverter(UnionShape unionShape) {
    final WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    final String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    delegator.useFileWriter(
      moduleName + "/smithy_to_dafny.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        // This hardcodes the input parameter name for a conversion function to always be
        // "native_input"
        String dataSourceInsideConversionFunction = "native_input";

        // ex. shape: simple.union.ExampleUnion
        // Writes `def SmithyToDafny_simple_union_ExampleUnion(input):`
        //   and wraps inner code inside function definition
        conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(
            unionShape,
            context
          ),
          dataSourceInsideConversionFunction,
          () -> {
            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            for (MemberShape memberShape : unionShape
              .getAllMembers()
              .values()) {
              Shape targetShape = context
                .model()
                .expectShape(memberShape.getTarget());
              // Write out conversion:
              // ex. if ExampleUnion can take on either of (IntegerValue, StringValue), write:
              // if isinstance(input, ExampleUnion.IntegerValue):
              //   example_union_union_value = DafnyExampleUnionIntegerValue(input.member.value)
              // elif isinstance(input, ExampleUnion.StringValue):
              //   example_union_union_value = DafnyExampleUnionIntegerValue(input.member.value)
              conversionWriter.write(
                """
                $L isinstance($L, $L.$L):
                    $L_union_value = $L($L)""",
                // If we need a new `if` block, open one; otherwise, expand on existing one
                // with `elif`
                shouldOpenNewIfBlock ? "if" : "elif",
                dataSourceInsideConversionFunction,
                SmithyNameResolver.getSmithyGeneratedModelLocationForShape(
                  unionShape.getId(),
                  context
                ),
                SmithyNameResolver.getSmithyGeneratedTypeForUnion(
                  unionShape,
                  memberShape,
                  context
                ),
                unionShape.getId().getName(),
                DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                targetShape.accept(
                  ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
                    targetShape,
                    context,
                    dataSourceInsideConversionFunction + ".value",
                    conversionWriter,
                    "smithy_to_dafny"
                  )
                )
              );
              shouldOpenNewIfBlock = false;

              DafnyNameResolver.importDafnyTypeForUnion(
                conversionWriter,
                unionShape,
                memberShape,
                context
              );
              SmithyNameResolver.importSmithyGeneratedTypeForShape(
                conversionWriter,
                unionShape,
                context
              );
            }

            // Write case to handle if union member does not match any of the above cases
            conversionWriter.write(
              """
              else:
                  raise ValueError("No recognized union value in union type: " + str($L))
              """,
              dataSourceInsideConversionFunction
            );

            // Return the result of the union conversion
            // `return example_union_union_value`
            conversionWriter.write(
              "return %1$s_union_value".formatted(unionShape.getId().getName())
            );
          }
        );
      }
    );
  }

  @Override
  protected void writeStringEnumShapeConverter(
    StringShape stringShapeWithEnumTrait
  ) {
    final WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    final String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    delegator.useFileWriter(
      moduleName + "/smithy_to_dafny.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        // This hardcodes the input parameter name for a conversion function to always be
        // "native_input"
        final String dataSourceInsideConversionFunction = "native_input";

        conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(
            stringShapeWithEnumTrait,
            context
          ),
          dataSourceInsideConversionFunction,
          () -> {
            // First enum value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            for (EnumDefinition enumDefinition : stringShapeWithEnumTrait
              .getTrait(EnumTrait.class)
              .get()
              .getValues()) {
              String name = enumDefinition.getName().isPresent()
                ? enumDefinition.getName().get()
                : enumDefinition.getValue();
              String value = enumDefinition.getValue();
              conversionWriter.openBlock(
                "$L $L == '$L':",
                "",
                shouldOpenNewIfBlock ? "if" : "elif",
                dataSourceInsideConversionFunction,
                value,
                () -> {
                  conversionWriter.write(
                    "return $L()",
                    DafnyNameResolver.getDafnyTypeForStringShapeWithEnumTrait(
                      stringShapeWithEnumTrait,
                      name
                    )
                  );
                  DafnyNameResolver.importDafnyTypeForStringShapeWithEnumTrait(
                    conversionWriter,
                    stringShapeWithEnumTrait,
                    name,
                    context
                  );
                }
              );
              shouldOpenNewIfBlock = false;
            }
            conversionWriter.openBlock(
              "else:",
              "",
              () -> {
                conversionWriter.write(
                  "raise ValueError(f'No recognized enum value in enum type: {$L=}')",
                  dataSourceInsideConversionFunction
                );
              }
            );
          }
        );
      }
    );
  }
}
