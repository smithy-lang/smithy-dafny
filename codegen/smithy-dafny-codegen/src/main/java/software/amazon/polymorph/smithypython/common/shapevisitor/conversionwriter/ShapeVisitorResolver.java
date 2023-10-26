package software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter;

import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.AwsSdkToDafnyShapeVisitor;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.DafnyToAwsSdkShapeVisitor;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.DafnyToLocalServiceShapeVisitor;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceToDafnyShapeVisitor;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

public class ShapeVisitorResolver {

  public static ShapeVisitor.Default<String> getToNativeShapeVisitorForShape(
      Shape shape,
      GenerationContext context,
      String dataSource,
      PythonWriter writer,
      String filename
  ) {
    if (AwsSdkNameResolver.isAwsSdkShape(shape)) {
      return new DafnyToAwsSdkShapeVisitor(context, dataSource, writer);
    } else {
      return new DafnyToLocalServiceShapeVisitor(context, dataSource, writer, filename);
    }
  }

  public static ShapeVisitor.Default<String> getToNativeShapeVisitorForShape(
      Shape shape,
      GenerationContext context,
      String dataSource,
      PythonWriter writer
  ) {
    if (AwsSdkNameResolver.isAwsSdkShape(shape)) {
      return new DafnyToAwsSdkShapeVisitor(context, dataSource, writer);
    } else {
      return new DafnyToLocalServiceShapeVisitor(context, dataSource, writer);
    }
  }

  public static ShapeVisitor.Default<String> getToDafnyShapeVisitorForShape(
      Shape shape,
      GenerationContext context,
      String dataSource,
      PythonWriter writer,
      String filename
  ) {
    if (AwsSdkNameResolver.isAwsSdkShape(shape)) {
      return new AwsSdkToDafnyShapeVisitor(context, dataSource, writer);
    } else {
      return new LocalServiceToDafnyShapeVisitor(context, dataSource, writer, filename);
    }
  }

  public static ShapeVisitor.Default<String> getToDafnyShapeVisitorForShape(
      Shape shape,
      GenerationContext context,
      String dataSource,
      PythonWriter writer
  ) {
    if (AwsSdkNameResolver.isAwsSdkShape(shape)) {
      return new AwsSdkToDafnyShapeVisitor(context, dataSource, writer);
    } else {
      return new LocalServiceToDafnyShapeVisitor(context, dataSource, writer);
    }
  }

}
