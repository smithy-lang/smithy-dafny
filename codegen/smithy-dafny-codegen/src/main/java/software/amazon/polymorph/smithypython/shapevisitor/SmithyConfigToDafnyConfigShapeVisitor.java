package software.amazon.polymorph.smithypython.shapevisitor;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
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
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * ShapeVisitor that should be dispatched from a Polymorph localService config shape
 * to generate code that maps a Smithy-modelled config shape's internal attributes
 * to the corresponding Dafny config shape's internal attributes.
 *
 * This largely defers to the SmithyToDafnyShapeVisitor implementation, except for StructureShapes.
 * Config StructureShape members are essentially required.
 */
public class SmithyConfigToDafnyConfigShapeVisitor extends SmithyToDafnyShapeVisitor.Default<String> {
    private final GenerationContext context;
    private final String dataSource;
    private final PythonWriter writer;
    private final String filename;

    /**
     * @param context The generation context.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code input.foo}, {@code entry}, etc.)
     */
    public SmithyConfigToDafnyConfigShapeVisitor(
        GenerationContext context,
        String dataSource,
        PythonWriter writer,
        String filename
    ) {
      this.context = context;
      this.dataSource = dataSource;
      this.writer = writer;
      this.filename = filename;
    }

  /**
   * Defers to SmithyToDafnyShapeVisitor by default.
   * @param shape Shape that is being visited.
   * @return
   */
  @Override
    protected String getDefault(Shape shape) {
      return shape.accept(
          new SmithyToDafnyShapeVisitor(context, dataSource, writer, filename)
      );
    }

    /**
     * Generates SmithyToDafny conversion logic for a Polymorph localService Config shape.
     * The provided StructureShape MUST be a Polymorph localService Config shape.
     * The primary
     * @param shape
     * @return
     */
    @Override
    public String structureShape(StructureShape shape) {
      return shape.accept(
          new SmithyToDafnyShapeVisitor(context, dataSource, writer, filename)
      );
//
//      if (!SmithyNameResolver.getLocalServiceConfigShapes(context).contains(shape.getId())) {
//        throw new CodegenException("Provided shape " + shape + " MUST be a localService config shape");
//      }
//
//      DafnyNameResolver.importDafnyTypeForShape(writer, shape.getId());
//      StringBuilder builder = new StringBuilder();
//      // Open Dafny structure shape
//      // e.g.
//      // DafnyStructureName(...
//      builder.append("%1$s(".formatted(DafnyNameResolver.getDafnyTypeForShape(shape)));
//      // Recursively dispatch a new ShapeVisitor for each member of the structure
//      for (Entry<String, MemberShape> memberShapeEntry : shape.getAllMembers().entrySet()) {
//        String memberName = memberShapeEntry.getKey();
//        MemberShape memberShape = memberShapeEntry.getValue();
//        final Shape targetShape = context.model().expectShape(memberShape.getTarget());
//
//        // Adds `DafnyStructureMember=smithy_structure_member(...)`
//        // e.g.
//        // DafnyStructureName(DafnyStructureMember=smithy_structure_member(...), ...)
//        // The nature of the `smithy_structure_member` conversion depends on the properties of the shape,
//        //   as described below
//        builder.append("%1$s=".formatted(memberName));
//
//        // If this is (another!) localService config shape, defer conversion to the config ShapeVisitor
//        if (SmithyNameResolver.getLocalServiceConfigShapes(context).contains(targetShape.getId())) {
//          builder.append("%1$s,\n".formatted(
//              targetShape.accept(
//                  new SmithyConfigToDafnyConfigShapeVisitor(
//                      context,
//                      dataSource + "." + CaseUtils.toSnakeCase(memberName),
//                      writer,
//                      filename
//                  )
//              )
//          ));
//        }
//        // Otherwise, treat this member as required, and defer to standard shape visitor
//        else {
//          builder.append("%1$s,\n".formatted(
//              targetShape.accept(
//                  new SmithyToDafnyShapeVisitor(
//                      context,
//                      dataSource + "." + CaseUtils.toSnakeCase(memberName),
//                      writer,
//                      filename
//                  )
//              )
//          ));
//        }
//      }
//
//      // Close structure
//      return builder.append(")").toString();
    }
}
