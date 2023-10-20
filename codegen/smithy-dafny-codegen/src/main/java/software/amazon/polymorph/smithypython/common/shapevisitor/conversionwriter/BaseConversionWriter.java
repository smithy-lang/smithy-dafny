package software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import software.amazon.polymorph.smithypython.wrappedlocalservice.DafnyPythonWrappedLocalServiceProtocolGenerator;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Abstract class for writing Dafny-to-X and X-to-Dafny conversion functions. (X = AWS SDK or LocalService.)
 * ShapeVisitors should call out to subclasses to write conversions for aggregate shapes (Unions and Structures
 *   TODO-Python: Can lists/maps contain themselves infinitely..?).
 * These shapes are special in that they can contain themselves as members,
 *   and require a function to
 * Sugclasses will write conversion functions for the provided shape and its members,
 *   unless it has already
 */
public abstract class BaseConversionWriter {
  // Store the set of shapes for which this ShapeVisitor (and ShapeVisitors that extend this)
  // have already generated a conversion function, so we only write each conversion function once.
  final Set<Shape> generatedShapes = new HashSet<>();
  final List<Shape> shapesToGenerate = new ArrayList<>();
  boolean generating = false;
  protected GenerationContext context;
  protected PythonWriter writer;

  /**
   * Writes a function that converts from the AWS SDK dict to the Dafny-modelled shape.
   *
   * @param shape
   * @param context
   * @param writer
   */
  public void baseWriteConverterForShapeAndMembers(Shape shape, GenerationContext context,
      PythonWriter writer) {
    this.context = context;
    this.writer = writer;
    // Do NOT write any converters for wrapped localServices.
    // The wrapped localService should ONLY generate a Shim class.
    // The Shim will use the converters generated as part of the localService.
    if (context.applicationProtocol()
          .equals(DafnyPythonWrappedLocalServiceProtocolGenerator.DAFNY_PYTHON_WRAPPED_LOCAL_SERVICE_PROTOCOL)) {
      return;
    }

    // Enqueue this shape if this class has not generated a converter for it or is not already in queue
    if (!generatedShapes.contains(shape) && !shapesToGenerate.contains(shape)) {
      shapesToGenerate.add(shape);
    }

    // If `writeConverterForShapeAndMembers` is called while already writing another converter,
    // do NOT write the new converter inside the definition of the in-progress converter.
    // `shape` will be picked up once the in-progress converter is finished.
    while (!generating && !shapesToGenerate.isEmpty()) {
      // Indicate to recursive calls that this class is writing a converter to delay w
      generating = true;

      Shape toGenerate = shapesToGenerate.remove(0);
      generatedShapes.add(toGenerate);

      if (toGenerate.isStructureShape()) {
        writeStructureShapeConverter(toGenerate.asStructureShape().get());
      } else if (toGenerate.isUnionShape()) {
        writeUnionShapeConverter(toGenerate.asUnionShape().get());
      }
      generating = false;
    }
  }

  protected abstract void writeStructureShapeConverter(StructureShape structureShape);

  protected abstract void writeUnionShapeConverter(UnionShape unionShape);

}
