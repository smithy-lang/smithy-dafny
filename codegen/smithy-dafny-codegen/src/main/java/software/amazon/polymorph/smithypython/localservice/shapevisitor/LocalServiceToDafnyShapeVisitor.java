// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.shapevisitor;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter.DafnyToLocalServiceConversionFunctionWriter;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter.LocalServiceToDafnyConversionFunctionWriter;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
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
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * ShapeVisitor that should be dispatched from a shape
 * to generate code that maps a Smithy-modelled shape's internal attributes
 * to the corresponding Dafny shape's internal attributes.
 *
 * This generates code in a `smithy_to_dafny.py` file.
 * The generated code consists of methods that convert from a Smithy-modelled shape
 *   to a Dafny-modelled shape.
 * Code that requires these conversions will call out to this file.
 */
public class LocalServiceToDafnyShapeVisitor
  extends ShapeVisitor.Default<String> {

  private final GenerationContext context;
  private final String dataSource;
  private final PythonWriter writer;
  private final String filename;

  /**
   * @param context The generation context.
   * @param dataSource The in-code location of the data to provide an output of
   *                   ({@code input.foo}, {@code entry}, etc.)
   */
  public LocalServiceToDafnyShapeVisitor(
    final GenerationContext context,
    final String dataSource,
    final PythonWriter writer,
    final String filename
  ) {
    this.context = context;
    this.dataSource = dataSource;
    this.writer = writer;
    this.filename = filename;
  }

  public LocalServiceToDafnyShapeVisitor(
    final GenerationContext context,
    final String dataSource,
    final PythonWriter writer
  ) {
    this.context = context;
    this.dataSource = dataSource;
    this.writer = writer;
    this.filename = "";
  }

  @Override
  protected String getDefault(Shape shape) {
    final String protocolName = context.protocolGenerator().getName();
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
    writer.addStdlibImport("_dafny", "Seq");
    return "Seq(" + dataSource + ")";
  }

  @Override
  public String structureShape(StructureShape structureShape) {
    // ONLY write converters if the shape under generation is in the current namespace (or Unit shape)
    if (
      structureShape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace()) ||
      SmithyNameResolver.isUnitShape(structureShape.getId())
    ) {
      LocalServiceToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(
        structureShape,
        context,
        writer
      );
      // Write the conversion method for the opposite direction to support WrappedLocalServices
      DafnyToLocalServiceConversionFunctionWriter.writeConverterForShapeAndMembers(
        structureShape,
        context,
        writer
      );
    }

    // Import the converter from where the ShapeVisitor was called
    final String pythonModuleName =
      SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
        structureShape.getId().getNamespace(),
        context
      );
    writer.addStdlibImport(pythonModuleName + ".smithy_to_dafny");

    // Return a reference to the generated conversion method
    // ex. for shape example.namespace.ExampleShape
    // returns
    // `example_namespace.smithygenerated.smithy_to_dafny.SmithyToDafny_example_namespace_ExampleShape(input)`
    return "%1$s.smithy_to_dafny.%2$s(%3$s)".formatted(
        pythonModuleName,
        SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(
          structureShape,
          context
        ),
        dataSource
      );
  }

  @Override
  public String listShape(ListShape shape) {
    writer.addStdlibImport("_dafny", "Seq");

    final StringBuilder builder = new StringBuilder();

    // Open Dafny sequence:
    // `Seq([`
    builder.append("Seq([");
    final MemberShape memberShape = shape.getMember();
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());

    // Add converted list elements into the list:
    // `Seq([`SmithyToDafny(list_element)``
    builder.append(
      "%1$s".formatted(
          targetShape.accept(
            ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
              targetShape,
              context,
              "list_element",
              writer
            )
          )
        )
    );

    // Close structure
    // `Seq([`SmithyToDafny(list_element)` for list_element in `dataSource`])``
    return builder
      .append(" for list_element in %1$s])".formatted(dataSource))
      .toString();
  }

  @Override
  public String mapShape(MapShape shape) {
    writer.addStdlibImport("_dafny", "Map");

    final StringBuilder builder = new StringBuilder();

    // Open Dafny map:
    // `Map({`
    builder.append("Map({");
    final MemberShape keyMemberShape = shape.getKey();
    final Shape keyTargetShape = context
      .model()
      .expectShape(keyMemberShape.getTarget());
    final MemberShape valueMemberShape = shape.getValue();
    final Shape valueTargetShape = context
      .model()
      .expectShape(valueMemberShape.getTarget());

    // Write converted map keys into the map:
    // `{`SmithyToDafny(key)`:`
    builder.append(
      "%1$s: ".formatted(
          keyTargetShape.accept(
            ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
              keyTargetShape,
              context,
              "key",
              writer
            )
          )
        )
    );

    // Write converted map values into the map:
    // `{`SmithyToDafny(key)`: `SmithyToDafny(value)``
    builder.append(
      "%1$s".formatted(
          valueTargetShape.accept(
            ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
              valueTargetShape,
              context,
              "value",
              writer
            )
          )
        )
    );

    // Complete map comprehension and close map
    // `{`SmithyToDafny(key)`: `SmithyToDafny(value)`` for (key, value) in `dataSource`.items() }`
    return builder
      .append(" for (key, value) in %1$s.items() })".formatted(dataSource))
      .toString();
  }

  @Override
  public String booleanShape(BooleanShape shape) {
    return dataSource;
  }

  @Override
  public String stringShape(StringShape shape) {
    writer.addStdlibImport("_dafny", "Seq");
    if (shape.hasTrait(DafnyUtf8BytesTrait.class)) {
      // Convert native Python string to Dafny Seq of UTF-8 bytes
      return "Seq(%1$s.encode('utf-8'))".formatted(dataSource);
    }
    // Convert native Python string to Dafny Seq of UTF-16 characters
    // TODO: This is a long conversion that is used often in generated code, since this is written for *all* strings.
    // This should be refactored into the conversionwriter package.
    return "Seq(''.join([chr(int.from_bytes(pair, 'big')) for pair in zip(*[iter(%1$s.encode('utf-16-be'))]*2)]))".formatted(
        dataSource
      );
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
    // ONLY write converters if the shape under generation is in the current namespace
    if (
      shape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
      LocalServiceToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(
        shape,
        context,
        writer
      );
      // Write the conversion method for the opposite direction to support WrappedLocalServices
      DafnyToLocalServiceConversionFunctionWriter.writeConverterForShapeAndMembers(
        shape,
        context,
        writer
      );
    }

    // Import the smithy_to_dafny converter from where the ShapeVisitor was called
    final String pythonModuleSmithygeneratedPath =
      SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
        shape.getId().getNamespace(),
        context
      );
    writer.addStdlibImport(
      pythonModuleSmithygeneratedPath + ".smithy_to_dafny"
    );

    // Return a reference to the generated conversion method
    // ex. for shape example.namespace.ExampleShape
    // returns
    // `example_namespace.smithygenerated.smithy_to_dafny.SmithyToDafny_example_namespace_ExampleShape(input)`
    return "%1$s.smithy_to_dafny.%2$s(%3$s)".formatted(
        pythonModuleSmithygeneratedPath,
        SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(shape, context),
        dataSource
      );
  }

  @Override
  public String timestampShape(TimestampShape shape) {
    throw new UnsupportedOperationException(
      "TimestampShape from within a LocalService not supported"
    );
  }

  @Override
  public String unionShape(UnionShape unionShape) {
    // ONLY write converters if the shape under generation is in the current namespace
    if (
      unionShape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
      LocalServiceToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(
        unionShape,
        context,
        writer
      );
      // Write the conversion method for the opposite direction to support WrappedLocalServices
      DafnyToLocalServiceConversionFunctionWriter.writeConverterForShapeAndMembers(
        unionShape,
        context,
        writer
      );
    }

    // Import the smithy_to_dafny converter from where the ShapeVisitor was called
    final String pythonModuleSmithygeneratedPath =
      SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
        unionShape.getId().getNamespace(),
        context
      );
    writer.addStdlibImport(
      pythonModuleSmithygeneratedPath + ".smithy_to_dafny"
    );

    // Return a reference to the generated conversion method
    // ex. for shape example.namespace.ExampleShape
    // returns
    // `example_namespace.smithygenerated.smithy_to_dafny.SmithyToDafny_example_namespace_ExampleShape(input)`
    return "%1$s.smithy_to_dafny.%2$s(%3$s)".formatted(
        pythonModuleSmithygeneratedPath,
        SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(
          unionShape,
          context
        ),
        dataSource
      );
  }
}
