package software.amazon.polymorph.smithyjava.modeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.generator.ToNative;
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
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.CollectionShape;
import software.amazon.smithy.model.shapes.DocumentShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.NumberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;

import java.nio.ByteBuffer;
import java.util.Arrays;
import java.util.Map;

public class ModeledNode {

    public static CodeBlock modeledValue(JavaLibrary subject, boolean base64BlobStrings, Shape shape, Node value) {
        return value.accept(new ValueNodeVisitor(subject, base64BlobStrings, shape));
    }

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

        private ValueNodeVisitor(JavaLibrary subject, boolean base64BlobStrings, Shape shape) {
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
                case STRUCTURE -> structureShape((StructureShape) shape, node);
//                case MAP -> mapShape((MapShape) inputShape, node);
//                case UNION -> unionShape((UnionShape) inputShape, node);
//                case DOCUMENT -> documentShape((DocumentShape) inputShape, node);
                default -> throw new CodegenException("unexpected input shape: " + shape.getType());
            };
        }

        private CodeBlock structureShape(StructureShape shape, ObjectNode node) {
            final TypeName inputType = subject.nativeNameResolver.typeForShape(shape.getId());
            CodeBlock.Builder result = CodeBlock.builder().add("$T.builder()", inputType);

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

        @Override
        public CodeBlock arrayNode(ArrayNode node) {
            // The target visitor won't change if the input shape is a union
            ValueNodeVisitor targetVisitor;
            if (shape instanceof CollectionShape) {
                var target = subject.model.expectShape(((CollectionShape) shape).getMember().getTarget());
                targetVisitor = visitorForShape(target);
            } else {
                targetVisitor = this;
            }

            CodeBlock elementsBlock = node.getElements().stream()
                    .map(n -> n.accept(targetVisitor))
                    .collect(CodeBlock.joining(",$W"));

            return CodeBlock.of("$T.asList($L)", ClassName.get(Arrays.class), elementsBlock);
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
                // ByteBuffer is correct since we're only using this for local services so far.
                TypeName byteBuffer = ClassName.get(ByteBuffer.class);
                String value = node.getValue();
                CodeBlock rawBytes;
                if (base64BlobStrings) {
                    rawBytes = CodeBlock.of("$T.decode($S)", Constants.BASE64_DECODER_CLASS_NAME, value);
                } else {
                    if (!value.matches("[A-Za-z0-9]*")) {
                        throw new IllegalArgumentException("Blob values must only contain alphanumeric characters");
                    }
                    rawBytes = CodeBlock.of("$S.getBytes($T.US_ASCII)", node.getValue(), Constants.STANDARD_CHARSETS_CLASS_NAME);
                }
                return CodeBlock.of("$T.wrap($L)", byteBuffer, rawBytes);
            } else if (shape.isFloatShape() || shape.isDoubleShape()) {
                throw new IllegalArgumentException("floating point shapes are not supported");
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
