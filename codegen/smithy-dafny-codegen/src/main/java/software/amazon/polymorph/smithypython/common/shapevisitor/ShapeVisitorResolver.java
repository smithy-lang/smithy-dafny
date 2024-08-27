// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.common.shapevisitor;

import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.AwsSdkToDafnyShapeVisitor;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.DafnyToAwsSdkShapeVisitor;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.DafnyToLocalServiceShapeVisitor;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceToDafnyShapeVisitor;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Utility class to return the correct ShapeVisitor for the provided Shape. If the shape is an AWS
 * SDK shape, returns an AWS SDK ShapeVisitor; otherwise, returns a LocalService ShapeVisitor. Two
 * usage notes:
 *
 * <p>1) LocalService ShapeVisitor MUST NOT directly defer to another LocalService ShapeVisitor.
 * LocalService shapes can depend on AWS SDK shapes, and this class is responsible for determining
 * which ShapeVisitor to defer to. AWS SDK ShapeVisitors CAN defer directly to an AWS SDK
 * ShapeVisitor, since AWS SDK shapes do not defer to LocalService shapes.
 *
 * <p>2) LocalService ShapeVisitor CAN defer directly to a LocalService ShapeVisitor and not use
 * this class if the targetShape is a LocalService Config shape.
 */
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
      return new DafnyToLocalServiceShapeVisitor(
        context,
        dataSource,
        writer,
        filename
      );
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
      return new LocalServiceToDafnyShapeVisitor(
        context,
        dataSource,
        writer,
        filename
      );
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
