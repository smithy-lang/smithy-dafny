package software.amazon.polymorph.smithyjava.modeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.generator.ToNative;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.node.NumberNode;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.node.StringNode;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.NumberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;

import java.util.Map;

public class ModeledNode {

    public static void declareModeledValue(JavaLibrary subject, MethodSpec.Builder method, String variableName, Shape shape, Node value) {
        switch (shape.getType()) {
            case STRUCTURE -> declareStructureValue(subject, method, variableName, (StructureShape)shape, (ObjectNode)value);
            case STRING -> declareStringValue(subject, method, variableName, (StringShape) shape, (StringNode)value);
            case INTEGER -> declareNumberValue(subject, method, variableName, (NumberShape) shape, (NumberNode)value);
            case BLOB -> declareBlobValue(subject, method, variableName, (BlobShape) shape, (StringNode)value);
            default -> throw new IllegalArgumentException("Node values of this shape type not yet supported: " + shape);
        }
    }

    private static void declareStructureValue(JavaLibrary subject, MethodSpec.Builder method, String variableName, StructureShape structureShape, ObjectNode value) {
        final TypeName inputType = subject.nativeNameResolver.typeForShape(structureShape.getId());
        final TypeName inputBuilderType = BuilderSpecs.builderInterfaceName((ClassName)inputType);

        method.addStatement("$T $LBuilder = $T.builder()", inputBuilderType, variableName, inputType);

        for (Map.Entry<String, Node> entry : value.getStringMap().entrySet()) {
            String memberName = entry.getKey();
            Node memberValue = entry.getValue();
            MemberShape memberShape = structureShape.getAllMembers().get(memberName);
            Shape targetShape = subject.model.expectShape(memberShape.getTarget());
            declareModeledValue(subject, method, memberName, targetShape, memberValue);
            // TODO: name munging
            method.addStatement("$LBuilder.$L($L)", variableName, memberName, memberName);
        }

        method.addStatement("$T $L = inputBuilder.build()", inputType, variableName);
    }

    private static void declareStringValue(JavaLibrary subject, MethodSpec.Builder method, String variableName, StringShape stringShape, StringNode value) {
        // TODO: escaping
        method.addStatement("String $L = \"$L\"", variableName, value.getValue());
    }

    private static void declareNumberValue(JavaLibrary subject, MethodSpec.Builder method, String variableName, NumberShape numberShape, NumberNode value) {
        TypeName typeName = subject.nativeNameResolver.typeForShape(numberShape.getId());
        method.addStatement("$T $L = $L", typeName, variableName, value.getValue());
    }

    private static void declareBlobValue(JavaLibrary subject, MethodSpec.Builder method, String variableName, BlobShape blobShape, StringNode value) {
        // Although https://smithy.io/2.0/spec/model.html#trait-node-values says the string value should be base64 encoded,
        // both https://smithy.io/2.0/additional-specs/http-protocol-compliance-tests.html
        // and https://smithy.io/2.0/additional-specs/smoke-tests.html
        // say "binary data MUST be defined using values that can be represented in plain text".
        // This is a bit ambiguous, so to be safe we only support ASCII.

    }
}
