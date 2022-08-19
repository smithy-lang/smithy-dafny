package software.amazon.polymorph.smithyjava.generator.awssdk;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;

import org.junit.Before;
import org.junit.Test;

import software.amazon.polymorph.smithyjava.ModelConstants;
import software.amazon.polymorph.util.TestModel;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.utils.StringUtils;

import static org.junit.Assert.assertEquals;
import static software.amazon.polymorph.smithyjava.ModelConstants.KMS_SIMPLE_SHAPES;
import static software.amazon.polymorph.smithyjava.generator.awssdk.Constants.DO_SOMETHING_REQUEST;
import static software.amazon.polymorph.smithyjava.generator.awssdk.Constants.DO_SOMETHING_RESPONSE;
import static software.amazon.polymorph.smithyjava.generator.awssdk.Constants.IDENTITY_NORMAL_REFERENCE;
import static software.amazon.polymorph.smithyjava.generator.awssdk.Constants.MESSAGE_ASSIGNMENT_OPTIONAL;
import static software.amazon.polymorph.smithyjava.generator.awssdk.Constants.MESSAGE_ASSIGNMENT_REQUIRED;
import static software.amazon.polymorph.smithyjava.generator.awssdk.Constants.MESSAGE_DECLARATION_OPTIONAL;
import static software.amazon.polymorph.smithyjava.generator.awssdk.Constants.MESSAGE_DECLARATION_REQUIRED;
import static software.amazon.polymorph.smithyjava.generator.awssdk.Constants.TO_DAFNY_BLOB_CONVERSION;
import static software.amazon.polymorph.smithyjava.generator.awssdk.Constants.TO_DAFNY_STRING_CONVERSION;
import static software.amazon.polymorph.smithyjava.nameresolver.AwsSdkHelpers.namespaceForService;
import static software.amazon.polymorph.utils.ModelUtils.serviceFromNamespace;

@SuppressWarnings("OptionalGetWithoutIsPresent")
public class ToDafnyTest {
    protected ToDafny underTest;

    @Before
    public void setup() {
        underTest = setupLocalModel(ModelConstants.KMS_A_STRING_OPERATION, "kms");
    }

    static ToDafny setupLocalModel(String rawModel, String awsName) {
        Model localModel = TestModel.setupModel(
                (builder, modelAssembler) -> modelAssembler
                        .addUnparsedModel("test.smithy", rawModel));
        ServiceShape serviceShape = serviceFromNamespace(
                localModel, namespaceForService(awsName));
        AwsSdk temp = new AwsSdk(serviceShape, localModel);
        return new ToDafny(temp);
    }

    @Test
    public void memberDeclarationStringRequired() {
        MemberShape memberShape = getMessageMemberShape(ShapeId.fromParts(
                "com.amazonaws.kms", "DoSomethingRequest"), underTest);
        CodeBlock variable = getMessageVariable(memberShape);
        String expected = MESSAGE_DECLARATION_REQUIRED;
        CodeBlock actual = this.underTest.memberDeclaration(memberShape, variable);
        assertEquals(expected, actual.toString());
    }

    @Test
    public void memberDeclarationStringOption() {
        MemberShape memberShape = getMessageMemberShape(ShapeId.fromParts(
                "com.amazonaws.kms", "DoSomethingResponse"), underTest);
        CodeBlock variable = getMessageVariable(memberShape);
        String expected = MESSAGE_DECLARATION_OPTIONAL;
        CodeBlock actual = this.underTest.memberDeclaration(memberShape, variable);
        assertEquals(expected, actual.toString());
    }

    @Test
    public void memberConversionBlob() {
        underTest = setupLocalModel(KMS_SIMPLE_SHAPES, "kms");
        MemberShape memberShape = getMemberShape(
                ShapeId.fromParts("com.amazonaws.kms", "Kitchen"),
                underTest, "ciphertext");
        String expected = TO_DAFNY_BLOB_CONVERSION;
        CodeBlock actual = underTest
                .memberConversionMethodReference(memberShape)
                .asNormalReference();
        assertEquals(expected, actual.toString());
    }

    @Test
    public void memberConversionBoolean() {
        underTest = setupLocalModel(KMS_SIMPLE_SHAPES, "kms");
        MemberShape memberShape = getMemberShape(
                ShapeId.fromParts("com.amazonaws.kms", "Kitchen"),
                underTest, "isTrue");
        String expected = IDENTITY_NORMAL_REFERENCE;
        CodeBlock actual = underTest
                .memberConversionMethodReference(memberShape)
                .asNormalReference();
        assertEquals(expected, actual.toString());
    }

    @Test
    public void memberConversionString() {
        underTest = setupLocalModel(KMS_SIMPLE_SHAPES, "kms");
        MemberShape memberShape = getMemberShape(
                ShapeId.fromParts("com.amazonaws.kms", "Kitchen"),
                underTest, "name");
        String expected = TO_DAFNY_STRING_CONVERSION;
        CodeBlock actual = underTest
                .memberConversionMethodReference(memberShape)
                .asNormalReference();
        assertEquals(expected, actual.toString());
    }

    @Test
    public void memberConversionTimestamp() {
        underTest = setupLocalModel(KMS_SIMPLE_SHAPES, "kms");
        MemberShape memberShape = getMemberShape(
                ShapeId.fromParts("com.amazonaws.kms", "Kitchen"),
                underTest, "creationDate");
        String expected = TO_DAFNY_STRING_CONVERSION;
        CodeBlock actual = underTest
                .memberConversionMethodReference(memberShape)
                .asNormalReference();
        assertEquals(expected, actual.toString());
    }

    @Test
    public void memberConversionInteger() {
        underTest = setupLocalModel(KMS_SIMPLE_SHAPES, "kms");
        MemberShape memberShape = getMemberShape(
                ShapeId.fromParts("com.amazonaws.kms", "Kitchen"),
                underTest, "limit");
        String expected = IDENTITY_NORMAL_REFERENCE;
        CodeBlock actual = underTest
                .memberConversionMethodReference(memberShape)
                .asNormalReference();
        assertEquals(expected, actual.toString());
    }

    @Test
    public void memberAssignmentStringRequired() {
        MemberShape memberShape = getMessageMemberShape(ShapeId.fromParts(
                "com.amazonaws.kms", "DoSomethingRequest"), underTest);
        CodeBlock variable = getMessageVariable(memberShape);
        String expected = MESSAGE_ASSIGNMENT_REQUIRED;
        CodeBlock actual = this.underTest.memberAssignment(memberShape, variable);
        assertEquals(expected, actual.toString());
    }

    @Test
    public void memberAssignmentStringOptional() {
        MemberShape memberShape = getMessageMemberShape(ShapeId.fromParts(
                "com.amazonaws.kms", "DoSomethingResponse"), underTest);
        CodeBlock variable = getMessageVariable(memberShape);
        String expected = MESSAGE_ASSIGNMENT_OPTIONAL;
        CodeBlock actual = this.underTest.memberAssignment(memberShape, variable);
        assertEquals(expected, actual.toString());
    }

    private static StructureShape getStructureByShapeId(ShapeId shapeId, ToDafny localUnderTest) {
        return localUnderTest.model.expectShape(shapeId, StructureShape.class);
    }

    private static MemberShape getMessageMemberShape(ShapeId shapeId, ToDafny localUnderTest) {
        return getMemberShape(shapeId, localUnderTest, "message");
    }

    private static MemberShape getMemberShape(ShapeId structureShapeId, ToDafny localUnderTest, String memberName) {
        StructureShape structureShape = getStructureByShapeId(structureShapeId, localUnderTest);
        return structureShape.getMember(memberName).get();
    }

    private static CodeBlock getMessageVariable(MemberShape memberShape) {
        return CodeBlock.of("$L", StringUtils.uncapitalize(memberShape.getMemberName()));
    }

    @Test
    public void responseStringRequired() {
        StructureShape structureShape = getStructureByShapeId(ShapeId.fromParts(
                "com.amazonaws.kms", "DoSomethingRequest"), underTest);
        String expected = DO_SOMETHING_REQUEST;
        MethodSpec actual = underTest.generateConvertResponse(structureShape.toShapeId());
        assertEquals(expected, actual.toString());
    }

    @Test
    public void responseStringOptional() {
        StructureShape structureShape = getStructureByShapeId(ShapeId.fromParts(
                "com.amazonaws.kms", "DoSomethingResponse"), underTest);
        String expected = DO_SOMETHING_RESPONSE;
        MethodSpec actual = underTest.generateConvertResponse(structureShape.toShapeId());
        assertEquals(expected, actual.toString());
    }

}
