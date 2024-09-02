// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import software.amazon.polymorph.smithypython.wrappedlocalservice.DafnyPythonWrappedLocalServiceProtocolGenerator;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Abstract class for writing Dafny-to-X and X-to-Dafny conversion functions. (X = AWS-SDK or
 * LocalService.) Subclasses of this class generate files that contain methods that convert from AWS
 * SDK shapes (i.e. boto3 request/response dictionaries) or native Python Smithy shapes to Dafny
 * shapes (Smithy-Dafny generated Dafny code transpiled into Python).
 *
 * <p>ShapeVisitors should call out to subclasses of this class to write conversions for aggregate
 * shapes that can contain themselves as members (Unions and Structures). These shapes require
 * delegating conversions to functions that recurse at runtime, and not at code generation time.
 */
public abstract class BaseConversionWriter {

  // Store the set of shapes for which the subclass has already generated conversion methods
  final Set<Shape> generatedShapes = new HashSet<>();
  // Queue of shapes to generate
  final List<Shape> shapesToGenerate = new ArrayList<>();
  // Flag to block generating inside a file while already generating another function
  // (prevents generating a conversion function inside another conversion function)
  // Note: This is not thread-safe. If Smithy-Dafny-Python runs from multiple threads,
  // this code won't work.
  // A mutex would prevent this.
  // SIM: https://sim.amazon.com/issues/CrypTool-5331
  boolean generating = false;

  protected GenerationContext context;
  // Writer pointing to the in-code location where the ShapeVisitor calling the subclass is writing
  protected PythonWriter writer;

  /**
   * Writes a function that converts from the AWS SDK dict to the Dafny-modelled shape. If the shape
   * has members that also require writing a conversion function, this function will also write
   * conversion methods for those shapes (recursively). If this method is called for the same shape
   * multiple times, subsequent calls will not write a conversion method for the shape. This is the
   * ONLY interface by which clients of this class' subclasses can request writing a new shape.
   *
   * @param shape
   * @param context
   * @param writer
   */
  public void baseWriteConverterForShapeAndMembers(
    Shape shape,
    GenerationContext context,
    PythonWriter writer
  ) {
    this.context = context;
    // Store where this is being written from where the original ShapeVisitor was dispatched (e.g.
    // serialize, shim);
    // This allows us to write imports in the original file
    this.writer = writer;
    // Do NOT write any converters for wrapped localServices.
    // The wrapped localService should ONLY generate a Shim class.
    // The Shim will use the converters generated as part of the localService.
    if (
      context
        .applicationProtocol()
        .equals(
          DafnyPythonWrappedLocalServiceProtocolGenerator.DAFNY_PYTHON_WRAPPED_LOCAL_SERVICE_PROTOCOL
        )
    ) {
      return;
    }

    // Enqueue this shape if this class has not generated a converter for it or is not already in
    // queue
    if (!generatedShapes.contains(shape) && !shapesToGenerate.contains(shape)) {
      shapesToGenerate.add(shape);
    }

    // If `writeConverterForShapeAndMembers` is called while already writing another converter,
    // do NOT write the new converter inside the definition of the in-progress converter.
    // `shape` will be picked up once the in-progress converter is finished.
    while (!generating && !shapesToGenerate.isEmpty()) {
      // Indicate to recursive calls that this class is writing a converter to
      //   prevent writing multiple conversion methods at once
      generating = true;

      Shape toGenerate = shapesToGenerate.remove(0);
      generatedShapes.add(toGenerate);

      if (toGenerate.isStructureShape()) {
        writeStructureShapeConverter(toGenerate.asStructureShape().get());
      } else if (toGenerate.isUnionShape()) {
        writeUnionShapeConverter(toGenerate.asUnionShape().get());
      } else if (
        toGenerate.isStringShape() && toGenerate.hasTrait(EnumTrait.class)
      ) {
        writeStringEnumShapeConverter(toGenerate.asStringShape().get());
      } else {
        throw new IllegalArgumentException(
          "Unsupported shape passed to ConversionWriter: " + toGenerate
        );
      }
      generating = false;
    }
  }

  protected abstract void writeStructureShapeConverter(
    StructureShape structureShape
  );

  protected abstract void writeUnionShapeConverter(UnionShape unionShape);

  protected abstract void writeStringEnumShapeConverter(
    StringShape stringShapeWithEnumTrait
  );
}
