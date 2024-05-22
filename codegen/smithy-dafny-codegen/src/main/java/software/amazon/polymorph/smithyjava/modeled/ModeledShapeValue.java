// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithyjava.modeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.TypeName;
import java.nio.ByteBuffer;
import java.util.Arrays;
import java.util.Map;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.nameresolver.Constants;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.model.node.ArrayNode;
import software.amazon.smithy.model.node.BooleanNode;
import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.node.NodeVisitor;
import software.amazon.smithy.model.node.NullNode;
import software.amazon.smithy.model.node.NumberNode;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.node.StringNode;
import software.amazon.smithy.model.shapes.CollectionShape;
import software.amazon.smithy.model.shapes.DocumentShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.UnionShape;

public class ModeledShapeValue {

  public static CodeBlock shapeValue(
    JavaLibrary subject,
    boolean base64BlobStrings,
    Shape shape,
    Node value
  ) {
    return value.accept(
      new ValueNodeVisitor(subject, base64BlobStrings, shape)
    );
  }

  // This algorithm is fundamentally a double dispatch,
  // and could have been a ShapeVisitor instead of a NodeVisitor.
  // That might have been somewhat cleaner since there are more Shape cases than Node cases,
  // and the same Node case is used across many shape cases (especially StringNode).
  // An immutable NodeVisitor is a good sweet spot in terms of performance, however,
  // since we can use the same visitor across all elements of a List, for example.
  private static class ValueNodeVisitor implements NodeVisitor<CodeBlock> {

    private final JavaLibrary subject;
    private final Shape shape;

    // https://smithy.io/2.0/spec/model.html#trait-node-values says the string value should be base64 encoded,
    // but both https://smithy.io/2.0/additional-specs/http-protocol-compliance-tests.html
    // and https://smithy.io/2.0/additional-specs/smoke-tests.html
    // say "binary data MUST be defined using values that can be represented in plain text".
    // Given this requirement is driven by making it easier to assert that data is automatically
    // base64 encoded in http protocol compliance tests,
    // which isn't as relevant for polymorph libraries,
    // we support either interpretation depending on this flag.
    // That way we can implement @smokeTests as specified
    // but use modeled node generation for other purposes that will want to
    // support arbitrary binary data.
    private final boolean base64BlobStrings;

    private ValueNodeVisitor(
      JavaLibrary subject,
      boolean base64BlobStrings,
      Shape shape
    ) {
      this.subject = subject;
      this.shape = shape;
      this.base64BlobStrings = base64BlobStrings;
    }

    private ValueNodeVisitor visitorForShape(Shape shape) {
      return new ValueNodeVisitor(subject, base64BlobStrings, shape);
    }

    @Override
    public CodeBlock objectNode(ObjectNode node) {
      return switch (shape.getType()) {
        case STRUCTURE, UNION -> structureOrUnionShape(shape, node);
        case MAP -> mapShape((MapShape) shape, node);
        case DOCUMENT -> documentShape((DocumentShape) shape, node);
        default -> throw new CodegenException(
          "unexpected input shape: " + shape.getType()
        );
      };
    }

    private CodeBlock structureOrUnionShape(Shape shape, ObjectNode node) {
      // The builder interfaces for structures and unions are identical,
      // the only difference is the constraint on only setting one member.
      if (shape instanceof UnionShape && node.getMembers().size() != 1) {
        throw new IllegalArgumentException(
          "Union shapes require an object node with exactly one member"
        );
      }

      final TypeName inputType = subject.nativeNameResolver.typeForShape(
        shape.getId()
      );
      CodeBlock.Builder result = CodeBlock
        .builder()
        .add("$T.builder()", inputType);

      for (Map.Entry<String, Node> entry : node.getStringMap().entrySet()) {
        String memberName = entry.getKey();
        Node memberValue = entry.getValue();

        MemberShape memberShape = shape.getAllMembers().get(memberName);
        Shape targetShape = subject.model.expectShape(memberShape.getTarget());

        CodeBlock memberExpr = memberValue.accept(visitorForShape(targetShape));

        result.add("\n.$N($L)", memberName, memberExpr);
      }

      return result.add("\n.build()").build();
    }

    private CodeBlock mapShape(MapShape shape, ObjectNode node) {
      final TypeName valueType = subject.nativeNameResolver.typeForShape(
        shape.getValue().getTarget()
      );
      final Shape valueShape = subject.model.expectShape(
        shape.getValue().getTarget()
      );
      final ValueNodeVisitor valueVisitor = visitorForShape(valueShape);

      CodeBlock entriesBlock = node
        .getMembers()
        .entrySet()
        .stream()
        .map(p ->
          CodeBlock.of(
            "put($S, $L);",
            p.getKey().getValue(),
            p.getValue().accept(valueVisitor)
          )
        )
        .collect(CodeBlock.joining("\n"));

      // Using the anonymous inner subclass trick
      // (new HashMap<String, Whatever>(){{ put("a", "b"); put("c", "d"); ... }})
      // because it's the easiest way to generate a map literal as an expression,
      // even though it's questionable in production code in general
      // because of the performance and garbage collection implications.
      // If we are really concerned we can create our own MapBuilder type in the future.
      return CodeBlock.of(
        "new $T<String, $T>() {{\n$L\n}}",
        Generator.Constants.JAVA_UTIL_HASHMAP,
        valueType,
        entriesBlock
      );
    }

    private CodeBlock documentShape(DocumentShape shape, Node node) {
      throw new IllegalArgumentException(
        "document node values are not supported"
      );
    }

    @Override
    public CodeBlock arrayNode(ArrayNode node) {
      var target = subject.model.expectShape(
        ((CollectionShape) shape).getMember().getTarget()
      );
      ValueNodeVisitor targetVisitor = visitorForShape(target);

      CodeBlock elementsBlock = node
        .getElements()
        .stream()
        .map(n -> n.accept(targetVisitor))
        .collect(CodeBlock.joining(",$W"));

      return CodeBlock.of(
        "$T.asList($L)",
        ClassName.get(Arrays.class),
        elementsBlock
      );
    }

    @Override
    public CodeBlock booleanNode(BooleanNode node) {
      return CodeBlock.of("$L", node.getValue());
    }

    @Override
    public CodeBlock numberNode(NumberNode node) {
      return CodeBlock.of("$L", node.getValue());
    }

    @Override
    public CodeBlock stringNode(StringNode node) {
      if (shape.isBlobShape()) {
        // ByteBuffer is the correct type since we're only using this for local services so far.
        // If we start supporting SDK-style services for some reason,
        // we'd also need to handle types like SdkBytes.
        TypeName byteBuffer = ClassName.get(ByteBuffer.class);
        String value = node.getValue();
        CodeBlock rawBytes;
        if (base64BlobStrings) {
          rawBytes =
            CodeBlock.of(
              "$T.decode($S)",
              Constants.BASE64_DECODER_CLASS_NAME,
              value
            );
        } else {
          // Be very conservative about "values that can be represented in plain text"
          // (as per the comment on base64BlobStrings)
          // since the specification is not specific.
          if (!value.matches("[A-Za-z0-9]*")) {
            throw new IllegalArgumentException(
              "Blob values must only contain alphanumeric characters"
            );
          }
          rawBytes =
            CodeBlock.of(
              "$S.getBytes($T.US_ASCII)",
              node.getValue(),
              Constants.STANDARD_CHARSETS_CLASS_NAME
            );
        }
        return CodeBlock.of("$T.wrap($L)", byteBuffer, rawBytes);
      } else if (shape.isFloatShape() || shape.isDoubleShape()) {
        throw new IllegalArgumentException(
          "floating point shapes are not yet supported"
        );
      } else {
        return CodeBlock.of("$S", node.getValue());
      }
    }

    @Override
    public CodeBlock nullNode(NullNode node) {
      throw new IllegalArgumentException("null node values are not supported");
    }
  }
}
