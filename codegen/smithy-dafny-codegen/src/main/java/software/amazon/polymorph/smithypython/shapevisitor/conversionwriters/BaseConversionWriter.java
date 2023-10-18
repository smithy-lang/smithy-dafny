package software.amazon.polymorph.smithypython.shapevisitor.conversionwriters;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

public abstract class BaseConversionWriter {
  // Store the set of shapes for which this ShapeVisitor (and ShapeVisitors that extend this)
  // have already generated a conversion function, so we only write each conversion function once.
  final Set<Shape> generatedShapes = new HashSet<>();
  final List<Shape> shapesToGenerate = new ArrayList<>();
  boolean generating = false;

  /**
   * Writes a function that converts from the AWS SDK dict to the Dafny-modelled shape.
   *
   * @param shape
   * @param context
   * @param writer
   * @param filename
   */
  public void writeConverterForShapeAndMembers(Shape shape, GenerationContext context,
      PythonWriter writer, String filename) {
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
        writeStructureShapeConverter(toGenerate.asStructureShape().get(), context, writer, filename);
      } else if (toGenerate.isUnionShape()) {
        writeUnionShapeConverter(toGenerate.asUnionShape().get(), context, writer, filename);
      }
      generating = false;
    }
  }

  abstract void writeStructureShapeConverter(StructureShape structureShape, GenerationContext context,
      PythonWriter writer, String filename);

  abstract void writeUnionShapeConverter(UnionShape unionShape, GenerationContext context,
      PythonWriter writer, String filename);
}
