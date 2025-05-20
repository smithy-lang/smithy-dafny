// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.shapevisitor;

import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.smithy.codegen.core.CodegenException;
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
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.StreamingTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.conversionwriters.AwsSdkFormatConversionFunctionWriter;

/**
 * ShapeVisitor that should be dispatched from a shape to generate code that parses a AWS SDK
 * kwarg-indexed dictionary for boto3 DynamoDB "expression strings" or AttributeValues
 * and passes those to functions that modify those members.
 */
public class AwsSdkFormatShapeVisitor extends ShapeVisitor.Default<String> {

  private static final String itemHandlerFieldName = "item_handler";
  private static final String conditionHandlerFieldName = "condition_handler";
  private final GenerationContext context;
  private final PythonWriter writer;
  private final String dataSource;

  /**
   * @param context The generation context.
   * @param dataSource The in-code location of the data to provide an output of ({@code output.foo},
   *     {@code entry}, etc.)
   * @param writer A PythonWriter pointing to the in-code location where the ShapeVisitor was called
   *     from
   */
  public AwsSdkFormatShapeVisitor(
    GenerationContext context,
    String dataSource,
    PythonWriter writer
  ) {
    this.context = context;
    this.dataSource = dataSource;
    this.writer = writer;
  }

  @Override
  protected String getDefault(Shape shape) {
    String protocolName = context.protocolGenerator().getName();
    throw new CodegenException(
      String.format(
        "Unsupported conversion of %s to %s using the %s protocol",
        shape,
        shape.getType(),
        protocolName
      )
    );
  }

  @Override
  public String blobShape(BlobShape shape) {
    return dataSource;
  }

  @Override
  public String structureShape(StructureShape structureShape) {
    if (SmithyNameResolver.isUnitShape(structureShape.getId())) {
      return "None";
    }

    // Conditionally write to/from conversion functions for structureShape
    AwsSdkFormatConversionFunctionWriter.writeConverterForShapeAndMembers(
      structureShape,
      context,
      writer
    );

    // Import the conversion function module from where the ShapeVisitor was called
    String pythonModuleName =
      SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
        structureShape.getId().getNamespace(),
        context
      );
    writer.addStdlibImport(pythonModuleName + ".aws_sdk_format_converter");

    // Return a reference to call the generated conversion method
    return "%1$s.aws_sdk_format_converter.%2$s(%3$s, %4$s, %5$s)".formatted(
        pythonModuleName,
        AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(structureShape),
        dataSource,
        itemHandlerFieldName,
        conditionHandlerFieldName
      );
  }

  @Override
  public String listShape(ListShape shape) {
    StringBuilder builder = new StringBuilder();

    // Open list:
    // `[`
    builder.append("[");
    MemberShape memberShape = shape.getMember();
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());

    // Add converted list elements into the list:
    // `[list_element for list_element in `AwsSdkFormatShapeVisitor(targetShape)``
    builder.append(
      "%1$s".formatted(
          targetShape.accept(
            new AwsSdkFormatShapeVisitor(context, "list_element", writer)
          )
        )
    );

    // Close structure:
    // `[list_element for list_element in `AwsSdkFormatShapeVisitor(targetShape)`]`
    return builder
      .append(" for list_element in %1$s]".formatted(dataSource))
      .toString();
  }

  @Override
  public String mapShape(MapShape shape) {
    StringBuilder builder = new StringBuilder();

    // Open map:
    // `{`
    builder.append("{");
    MemberShape keyMemberShape = shape.getKey();
    final Shape keyTargetShape = context
      .model()
      .expectShape(keyMemberShape.getTarget());
    MemberShape valueMemberShape = shape.getValue();
    final Shape valueTargetShape = context
      .model()
      .expectShape(valueMemberShape.getTarget());

    // Write converted map keys into the map:
    // `{`AwsSdkFormatShapeVisitor(key)`:`
    builder.append(
      "%1$s: ".formatted(
          keyTargetShape.accept(
            new AwsSdkFormatShapeVisitor(context, "key", writer)
          )
        )
    );

    // Write converted map values into the map:
    // `{`AwsSdkFormatShapeVisitor(key)`: `AwsSdkFormatShapeVisitor(value)``
    builder.append(
      "%1$s".formatted(
          valueTargetShape.accept(
            new AwsSdkFormatShapeVisitor(context, "value", writer)
          )
        )
    );

    // Complete map comprehension and close map
    // `{`AwsSdkFormatShapeVisitor(key)`: `AwsSdkFormatShapeVisitor(value)`` for (key, value) in `dataSource`.items }`
    return builder
      .append(" for (key, value) in %1$s.items() }".formatted(dataSource))
      .toString();
  }

  @Override
  public String booleanShape(BooleanShape shape) {
    return dataSource;
  }

  @Override
  public String stringShape(StringShape shape) {
    // The only special strings are "expression strings."
    // If the string is an "expression string", call the condition_handler function.
    if (shape.getId().equals(ShapeId.from("com.amazonaws.dynamodb#ConditionExpression"))
        || shape.getId().equals(ShapeId.from("com.amazonaws.dynamodb#KeyExpression"))) {
      return "condition_handler(%1$s)".formatted(dataSource);
    }
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
    AwsSdkFormatConversionFunctionWriter.writeConverterForShapeAndMembers(
      shape,
      context,
      writer
    );
    // Import the aws_sdk_format_converter converter from where the ShapeVisitor was called
    String pythonModuleSmithygeneratedPath =
      SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
        shape.getId().getNamespace(),
        context
      );
    writer.addStdlibImport(
      pythonModuleSmithygeneratedPath + ".aws_sdk_format_converter"
    );

    // Return a reference to the generated conversion method
    return "%1$s.aws_sdk_format_converter.%2$s(%3$s, %4$s, %5$s)".formatted(
        pythonModuleSmithygeneratedPath,
        AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(shape),
        dataSource,
        itemHandlerFieldName,
        conditionHandlerFieldName
      );
  }

  @Override
  public String timestampShape(TimestampShape shape) {
    return dataSource;
  }

  @Override
  public String unionShape(UnionShape unionShape) {
    // The only special unionShape is AttributeValue.
    // Pass it to item_handler.
    if (unionShape.getId().equals(ShapeId.from("com.amazonaws.dynamodb#AttributeValue"))) {
        return "item_handler(%1$s)".formatted(dataSource);
    }

    AwsSdkFormatConversionFunctionWriter.writeConverterForShapeAndMembers(
      unionShape,
      context,
      writer
    );

    // Import the converter from where the ShapeVisitor was called
    String pythonModuleName =
      SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
        unionShape.getId().getNamespace(),
        context
      );
    writer.addStdlibImport(pythonModuleName + ".aws_sdk_format_converter");

    // Return a reference to the generated conversion method
    // ex. for shape example.namespace.ExampleShape
    // returns
    // `example_namespace.smithygenerated.aws_sdk_format_converter.example_namespace_ExampleShape(input)`
    return "%1$s.aws_sdk_format_converter.%2$s(%3$s, %4$s, %5$s)".formatted(
        pythonModuleName,
        AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(unionShape),
        dataSource,
        itemHandlerFieldName,
        conditionHandlerFieldName
      );
  }
}
