// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter.BaseConversionWriter;
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

/**
 * Writes the dafny_to_smithy.py file via the BaseConversionWriter implementation.
 */
public class DafnyToLocalServiceConversionFunctionWriter
  extends BaseConversionWriter {

  // Use a singleton to preserve generatedShapes through multiple invocations of this class
  static DafnyToLocalServiceConversionFunctionWriter singleton;

  protected DafnyToLocalServiceConversionFunctionWriter() {}

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
      moduleName + "/dafny_to_smithy.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        // This hardcodes the input parameter name for a conversion function to always be "dafny_input"
        final String dataSourceInsideConversionFunction = "dafny_input";

        conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(
            structureShape,
            context
          ),
          SmithyNameResolver.isUnitShape(structureShape.getId())
            ? ""
            : dataSourceInsideConversionFunction,
          () -> {
            if (structureShape.hasTrait(ReferenceTrait.class)) {
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
              writeTraitlessStructureShapeConverter(
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

  private void writeTraitlessStructureShapeConverter(
    StructureShape shape,
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction
  ) {
    // Only write top-level import for a shape in `.models` to avoid introducing a circular dependency
    if (
      SmithyNameResolver
        .getSmithyGeneratedModuleFilenameForSmithyShape(shape, context)
        .equals(".models")
    ) {
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        conversionWriter,
        shape,
        context
      );
    } else {
      conversionWriter.writeComment(
        "Deferred import of %1$s to avoid circular dependency".formatted(
            SmithyNameResolver.getSmithyGeneratedModuleFilenameForSmithyShape(
              shape,
              context
            )
          )
      );
      conversionWriter.write(
        "import $L",
        SmithyNameResolver.getSmithyGeneratedModelLocationForShape(
          shape,
          context
        )
      );
    }
    // Open Smithy structure shape
    // e.g.
    // smithy_structure_name(...
    conversionWriter.openBlock(
      "return $L(",
      ")",
      SmithyNameResolver.getSmithyGeneratedModelLocationForShape(
        shape.getId(),
        context
      ) +
      "." +
      context.symbolProvider().toSymbol(shape).getName(),
      () -> {
        // Recursively dispatch a new ShapeVisitor for each member of the structure
        for (Entry<String, MemberShape> memberShapeEntry : shape
          .getAllMembers()
          .entrySet()) {
          final String memberName = memberShapeEntry.getKey();
          final MemberShape memberShape = memberShapeEntry.getValue();
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

    conversionWriter.writeInline("$L=", CaseUtils.toSnakeCase(memberName));

    // Reference member shapes:
    // Optional: `member_name=ShapeVisitor(input.MemberName.UnwrapOr(None))`
    // Required: `member_name=ShapeVisitor(input.MemberName)`
    if (
      context
        .model()
        .expectShape(memberShape.getTarget())
        .hasTrait(ReferenceTrait.class)
    ) {
      conversionWriter.write(
        "($1L) if ($2L is not None) else None,",
        targetShape.accept(
          ShapeVisitorResolver.getToNativeShapeVisitorForShape(
            targetShape,
            context,
            dataSourceInsideConversionFunction +
            "." +
            memberName +
            (memberShape.isOptional() ? ".UnwrapOr(None)" : ""),
            conversionWriter,
            "dafny_to_smithy"
          )
        ),
        dataSourceInsideConversionFunction +
        "." +
        memberName +
        (memberShape.isOptional() ? ".UnwrapOr(None)" : "")
      );
    }
    // Optional non-reference member shapes:
    // `(ShapeVisitor(input.value)) if (input.value.is_Some) else None`
    else if (memberShape.isOptional()) {
      conversionWriter.write(
        "($L) if ($L.is_Some) else None,",
        targetShape.accept(
          ShapeVisitorResolver.getToNativeShapeVisitorForShape(
            targetShape,
            context,
            dataSourceInsideConversionFunction + "." + memberName + ".value",
            conversionWriter,
            "dafny_to_smithy"
          )
        ),
        dataSourceInsideConversionFunction + "." + memberName
      );
      // Required non-reference member shapes:
      // `ShapeVisitor(input.value)`
    } else {
      conversionWriter.write(
        "$L,",
        targetShape.accept(
          ShapeVisitorResolver.getToNativeShapeVisitorForShape(
            targetShape,
            context,
            dataSourceInsideConversionFunction + "." + memberName,
            conversionWriter,
            "dafny_to_smithy"
          )
        )
      );
    }
  }

  /**
   * Called from the StructureShape converter when the StructureShape has a Polymorph Positional trait.
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

    String returnValue = targetShape.accept(
      ShapeVisitorResolver.getToNativeShapeVisitorForShape(
        targetShape,
        context,
        dataSourceInsideConversionFunction,
        conversionWriter,
        "dafny_to_smithy"
      )
    );

    if (onlyMember.isOptional()) {
      conversionWriter.openBlock(
        "if $L.is_Some:",
        "",
        dataSourceInsideConversionFunction,
        () -> {
          conversionWriter.write("return $L", returnValue);
        }
      );
    } else {
      conversionWriter.write("return $L", returnValue);
    }
  }

  /**
   * Called from the StructureShape converter when the StructureShape has a Polymorph Reference trait.
   * @param structureShape
   * @return
   */
  private void writeReferenceStructureShapeConverter(
    StructureShape structureShape,
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction
  ) {
    final ReferenceTrait referenceTrait = structureShape.expectTrait(
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
        "Unknown referenceStructureShape type: " + structureShape
      );
    }
  }

  private void writeResourceShapeConverter(
    ResourceShape resourceShape,
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction
  ) {
    conversionWriter.openBlock(
      "if hasattr($L, '_native_impl'):",
      "",
      dataSourceInsideConversionFunction,
      () ->
        conversionWriter.write(
          "return $L._native_impl",
          dataSourceInsideConversionFunction
        )
    );

    conversionWriter.openBlock(
      "else:",
      "",
      () -> {
        // Import resource at runtime to avoid circular dependency
        conversionWriter.write(
          "from $L import $L",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            resourceShape.getId().getNamespace(),
            context
          ) +
          ".references",
          resourceShape.getId().getName()
        );

        conversionWriter.write(
          "return $L(_impl=$L)",
          resourceShape.getId().getName(),
          dataSourceInsideConversionFunction
        );
      }
    );
  }

  private void writeServiceShapeConverter(
    ServiceShape serviceShape,
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction
  ) {
    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      // Import resource at runtime to avoid circular dependency
      conversionWriter.write(
        "from $L import $L",
        SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
          serviceShape.getId().getNamespace(),
          context
        ) +
        ".client",
        serviceShape.getId().getName()
      );

      conversionWriter.write(
        "return $L(config=None, dafny_client=$L)",
        serviceShape.getId().getName(),
        dataSourceInsideConversionFunction
      );
    } else {
      conversionWriter.write("return dafny_input._impl");
    }
  }

  /**
   * Writes a function definition to convert a Dafny-modelled union shape
   *   into the corresponding Smithy-modelled union shape.
   * The function definition is written into `dafny_to_smithy.py`.
   * This SHOULD only be called once so only one function definition is written.
   * @param unionShape
   */
  @Override
  protected void writeUnionShapeConverter(UnionShape unionShape) {
    final WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    final String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    // Write out common conversion function inside dafny_to_smithy
    delegator.useFileWriter(
      moduleName + "/dafny_to_smithy.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        String dataSourceInsideConversionFunction = "dafny_input";

        // ex. shape: simple.union.ExampleUnion
        // Writes `def DafnyToSmithy_simple_union_ExampleUnion(input):`
        //   and wraps inner code inside function definition
        conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(
            unionShape,
            context
          ),
          dataSourceInsideConversionFunction,
          () -> {
            conversionWriter.writeComment(
              "Convert %1$s".formatted(unionShape.getId().getName())
            );

            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            // Write out conversion:
            // ex. if ExampleUnion can take on either of (IntegerValue, StringValue), write:
            // if isinstance(input, ExampleUnion_IntegerValue):
            //   ExampleUnion_union_value = ExampleUnionIntegerValue(input.IntegerValue)
            // elif isinstance(input, ExampleUnion_StringValue):
            //   ExampleUnion_union_value = ExampleUnionStringValue(input.StringValue)
            for (MemberShape memberShape : unionShape
              .getAllMembers()
              .values()) {
              Shape targetShape = context
                .model()
                .expectShape(memberShape.getTarget());
              conversionWriter.write(
                """
                $L isinstance($L, $L):
                    $L_union_value = $L.$L($L)""",
                // If we need a new `if` block, open one; otherwise, expand on existing one with `elif`
                shouldOpenNewIfBlock ? "if" : "elif",
                dataSourceInsideConversionFunction,
                DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                unionShape.getId().getName(),
                SmithyNameResolver.getSmithyGeneratedModelLocationForShape(
                  unionShape.getId(),
                  context
                ),
                SmithyNameResolver.getSmithyGeneratedTypeForUnion(
                  unionShape,
                  memberShape,
                  context
                ),
                targetShape.accept(
                  ShapeVisitorResolver.getToNativeShapeVisitorForShape(
                    targetShape,
                    context,
                    dataSourceInsideConversionFunction +
                    "." +
                    DafnyNameResolver.escapeShapeName(
                      memberShape.getMemberName()
                    ),
                    conversionWriter,
                    "dafny_to_smithy"
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
      moduleName + "/dafny_to_smithy.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        // This hardcodes the input parameter name for a conversion function to always be "dafny_input"
        String dataSourceInsideConversionFunction = "dafny_input";

        conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(
            stringShapeWithEnumTrait,
            context
          ),
          dataSourceInsideConversionFunction,
          () -> {
            EnumTrait enumTrait = stringShapeWithEnumTrait
              .getTrait(EnumTrait.class)
              .get();

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
              conversionWriter.write(
                """
                $L isinstance($L, $L):
                    return '$L'
                """,
                // If we need a new `if` block, open one; otherwise, expand on existing one
                // with `elif`
                shouldOpenNewIfBlock ? "if" : "elif",
                dataSourceInsideConversionFunction,
                DafnyNameResolver.getDafnyTypeForStringShapeWithEnumTrait(
                  stringShapeWithEnumTrait,
                  name
                ),
                value
              );
              shouldOpenNewIfBlock = false;

              DafnyNameResolver.importDafnyTypeForStringShapeWithEnumTrait(
                conversionWriter,
                stringShapeWithEnumTrait,
                name,
                context
              );
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
