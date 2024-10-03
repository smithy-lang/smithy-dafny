// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.shapevisitor.conversionwriters;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.AwsSdkToDafnyShapeVisitor;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter.BaseConversionWriter;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/** Writes the aws_sdk_to_dafny.py file via the BaseConversionWriter implementation. */
public class AwsSdkToDafnyConversionFunctionWriter
  extends BaseConversionWriter {

  // Use a singleton to preserve generatedShapes through multiple generations
  static AwsSdkToDafnyConversionFunctionWriter singleton;

  // Instantiate singleton at class-load time
  static {
    singleton = new AwsSdkToDafnyConversionFunctionWriter();
  }

  private AwsSdkToDafnyConversionFunctionWriter() {}

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

  protected void writeStructureShapeConverter(StructureShape structureShape) {
    if (structureShape.hasTrait(ErrorTrait.class)) {
      writeErrorStructureShapeConverter(structureShape);
      return;
    }

    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    delegator.useFileWriter(
      moduleName + "/aws_sdk_to_dafny.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        // This hardcodes the input parameter neme for a conversion function to always be "native_input"

        DafnyNameResolver.importDafnyTypeForShape(
          conversionWriter,
          structureShape.getId(),
          context
        );

        conversionWriter.openBlock(
          "def $L($L):",
          "",
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(
            structureShape
          ),
          "native_input",
          () -> {
            // Open Dafny structure shape
            // e.g.
            // DafnyStructureName(...
            String dataSourceInsideConversionFunction = "native_input";
            conversionWriter.openBlock(
              "return $L(",
              ")",
              structureShape.hasTrait(ErrorTrait.class)
                ? DafnyNameResolver.getDafnyTypeForError(structureShape)
                : DafnyNameResolver.getDafnyTypeForShape(structureShape),
              () -> {
                for (final Entry<
                  String,
                  MemberShape
                > memberShapeEntry : structureShape
                  .getAllMembers()
                  .entrySet()) {
                  String memberName = memberShapeEntry.getKey();
                  MemberShape memberShape = memberShapeEntry.getValue();

                  if (structureShape.hasTrait(ErrorTrait.class)) {
                    writeErrorStructureShapeMemberConverter(
                      conversionWriter,
                      dataSourceInsideConversionFunction,
                      memberName,
                      memberShape
                    );
                  } else {
                    writeStructureShapeMemberConverter(
                      conversionWriter,
                      dataSourceInsideConversionFunction,
                      memberName,
                      memberShape
                    );
                  }
                }
              }
            );
          }
        );
      }
    );
  }

  protected void writeErrorStructureShapeConverter(
    StructureShape structureShape
  ) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    delegator.useFileWriter(
      moduleName + "/aws_sdk_to_dafny.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        // This hardcodes the input parameter name for a conversion function to always be "native_input"
        String dataSourceInsideConversionFunction = "native_input";

        DafnyNameResolver.importDafnyTypeForShape(
          conversionWriter,
          structureShape.getId(),
          context
        );

        conversionWriter.openBlock(
          "def $L($L):",
          "",
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(
            structureShape
          ),
          dataSourceInsideConversionFunction,
          () -> {
            // Open Dafny structure shape
            // e.g.
            // DafnyStructureName(...
            conversionWriter.openBlock(
              "return $L(",
              ")",
              structureShape.hasTrait(ErrorTrait.class)
                ? DafnyNameResolver.getDafnyTypeForError(structureShape)
                : DafnyNameResolver.getDafnyTypeForShape(structureShape),
              () -> {
                for (Entry<
                  String,
                  MemberShape
                > memberShapeEntry : structureShape
                  .getAllMembers()
                  .entrySet()) {
                  String memberName = memberShapeEntry.getKey();
                  MemberShape memberShape = memberShapeEntry.getValue();
                  String memberShapeDataSource;
                  if (
                    shapeMemberIsOnResponseRoot(memberShape, structureShape)
                  ) {
                    memberShapeDataSource = dataSourceInsideConversionFunction;
                  } else {
                    memberShapeDataSource =
                      dataSourceInsideConversionFunction + "['Error']";
                  }
                  writeErrorStructureShapeMemberConverter(
                    conversionWriter,
                    memberShapeDataSource,
                    memberName,
                    memberShape
                  );
                }
              }
            );
          }
        );
      }
    );
  }

  /**
   * Returns true if the error value is on the root of the response,
   * rather than on the response's `['Error']` attribute.
   * This is not a common case.
   * @param memberShape
   * @param structureShape
   * @return
   */
  private boolean shapeMemberIsOnResponseRoot(
    MemberShape memberShape,
    StructureShape structureShape
  ) {
    // Case: TransactionCanceledException.CancellationReasons
    if (
      "CancellationReasons".equals(memberShape.getMemberName()) &&
      "TransactionCanceledException".equals(structureShape.getId().getName()) &&
      "com.amazonaws.dynamodb".equals(structureShape.getId().getNamespace())
    ) {
      return true;
    }
    return false;
  }

  private void writeErrorStructureShapeMemberConverter(
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

    // `message` members on Error shapes are actually accessed as `Message`
    if ("message".equals(memberName)) {
      memberName = "Message";
    }

    // Error structure members are always required
    conversionWriter.write(
      "$L,",
      targetShape.accept(
        new AwsSdkToDafnyShapeVisitor(
          context,
          dataSourceInsideConversionFunction + "[\"" + memberName + "\"]",
          conversionWriter
        )
      )
    );
  }

  private void writeStructureShapeMemberConverter(
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
    // shape, as described below
    conversionWriter.writeInline("$L=", memberName);

    // If this shape is optional, write conversion logic to detect and possibly pass
    //   an empty optional at runtime
    if (memberShape.isOptional()) {
      conversionWriter.addStdlibImport(
        "smithy_dafny_standard_library.internaldafny.generated.Wrappers",
        "Option_Some"
      );
      conversionWriter.addStdlibImport(
        "smithy_dafny_standard_library.internaldafny.generated.Wrappers",
        "Option_None"
      );
      conversionWriter.write(
        "Option_Some($L) if \"$L\" in $L.keys() else Option_None(),",
        targetShape.accept(
          new AwsSdkToDafnyShapeVisitor(
            context,
            dataSourceInsideConversionFunction + "[\"" + memberName + "\"]",
            conversionWriter
          )
        ),
        memberName,
        dataSourceInsideConversionFunction
      );
    }
    // If this shape is required, pass in the shape for conversion without any optional-checking
    else {
      conversionWriter.write(
        "$L,",
        targetShape.accept(
          new AwsSdkToDafnyShapeVisitor(
            context,
            dataSourceInsideConversionFunction + "[\"" + memberName + "\"]",
            conversionWriter
          )
        )
      );
    }
  }

  /**
   * Writes a function definition to convert a Smithy-modelled union shape into the corresponding
   * Dafny-modelled union shape. The function definition is written into `aws_sdk_to_dafny.py`. This
   * SHOULD only be called once so only one function definition is written.
   *
   * @param unionShape
   */
  protected void writeUnionShapeConverter(UnionShape unionShape) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    delegator.useFileWriter(
      moduleName + "/aws_sdk_to_dafny.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        // This hardcodes the input parameter name for a conversion function to always be "native_input"
        String dataSourceInsideConversionFunction = "native_input";

        // ex. shape: simple.union.ExampleUnion
        // Writes `def SmithyToDafny_simple_union_ExampleUnion(input):`
        //   and wraps inner code inside function definition
        conversionWriter.openBlock(
          "def $L($L):",
          "",
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(unionShape),
          dataSourceInsideConversionFunction,
          () -> {
            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            for (final MemberShape memberShape : unionShape
              .getAllMembers()
              .values()) {
              final Shape targetShape = context
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
                $L "$L" in $L.keys():
                    $L_union_value = $L($L)""",
                // If we need a new `if` block, open one; otherwise, expand on existing one
                // with `elif`
                shouldOpenNewIfBlock ? "if" : "elif",
                memberShape.getMemberName(),
                dataSourceInsideConversionFunction,
                unionShape.getId().getName(),
                DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                targetShape.accept(
                  new AwsSdkToDafnyShapeVisitor(
                    context,
                    dataSourceInsideConversionFunction +
                    "[\"" +
                    memberShape.getMemberName() +
                    "\"]",
                    conversionWriter
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

  /**
   * @param stringShapeWithEnumTrait
   */
  public void writeStringEnumShapeConverter(
    StringShape stringShapeWithEnumTrait
  ) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    // Write out common conversion function inside dafny_to_aws_sdk
    delegator.useFileWriter(
      moduleName + "/aws_sdk_to_dafny.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        String dataSourceInsideConversionFunction = "native_input";

        // ex. shape: simple.union.ExampleUnion
        // Writes `def DafnyToSmithy_simple_union_ExampleUnion(input):`
        //   and wraps inner code inside function definition
        conversionWriter.openBlock(
          "def $L($L):",
          "",
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(
            stringShapeWithEnumTrait
          ),
          dataSourceInsideConversionFunction,
          () -> {
            conversionWriter.writeComment(
              "Convert %1$s".formatted(
                  stringShapeWithEnumTrait.getId().getName()
                )
            );

            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            // Write out conversion:
            // ex. if ExampleUnion can take on either of (IntegerValue, StringValue), write:
            // if isinstance(input, ExampleUnion_IntegerValue):
            //   ExampleUnion_union_value = ExampleUnionIntegerValue(input.IntegerValue)
            // elif isinstance(input, ExampleUnion_StringValue):
            //   ExampleUnion_union_value = ExampleUnionStringValue(input.StringValue)

            for (final EnumDefinition enumDefinition : stringShapeWithEnumTrait
              .getTrait(EnumTrait.class)
              .get()
              .getValues()) {
              String value = enumDefinition.getValue();
              conversionWriter.write(
                """
                $L $L == "$L":
                    return $L()""",
                // If we need a new `if` block, open one; otherwise, expand on existing one
                // with `elif`
                shouldOpenNewIfBlock ? "if" : "elif",
                dataSourceInsideConversionFunction,
                value,
                DafnyNameResolver.getDafnyTypeForStringShapeWithEnumTrait(
                  stringShapeWithEnumTrait,
                  value
                )
              );
              shouldOpenNewIfBlock = false;

              DafnyNameResolver.importDafnyTypeForStringShapeWithEnumTrait(
                conversionWriter,
                stringShapeWithEnumTrait,
                value,
                context
              );
            }

            // Write case to handle if union member does not match any of the above cases
            conversionWriter.write(
              """
              else:
                  raise ValueError("No recognized enum value in enum type: " + $L)
              """,
              dataSourceInsideConversionFunction
            );
          }
        );
      }
    );
  }
}
