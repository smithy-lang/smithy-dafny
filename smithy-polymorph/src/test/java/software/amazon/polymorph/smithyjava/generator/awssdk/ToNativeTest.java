package software.amazon.polymorph.smithyjava.generator.awssdk;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;

import org.junit.Before;
import org.junit.Test;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.ModelConstants;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

import static org.junit.Assert.assertNull;
import static software.amazon.polymorph.smithyjava.generator.awssdk.ToNativeConstants.KEY_USAGE_TYPE;
import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

@SuppressWarnings("OptionalGetWithoutIsPresent")
public class ToNativeTest {
    protected ToNative underTest;
    protected Model model;

    @Before
    public void setup() {
        model = TestSetupUtils.setupTwoLocalModel(ModelConstants.KMS_KITCHEN, ModelConstants.OTHER_NAMESPACE);
        underTest  = new ToNative(TestSetupUtils.setupAwsSdk(model, "kms"));
    }

    @Test
    public void toNative() {
    }

    @Test
    public void generateConvert() {
    }

    @Test
    public void generateConvertSet() {
    }

    @Test
    public void generateConvertMap() {
    }

    @Test
    public void generateConvertList() {
    }

    @Test
    public void generateConvertStructure() {
    }

    @Test
    public void getMemberField() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        MemberShape stringMember = structureShape.getMember("name").get();
        CodeBlock actual = underTest.getMemberField(stringMember);
        String expected = "Name";
        tokenizeAndAssertEqual(expected, actual.toString());
    }

    @Test
    public void getMemberFieldValue() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        // if required, get via Field
        MemberShape requiredMember = structureShape.getMember("name").get();
        CodeBlock actualRequired = underTest.getMemberFieldValue(requiredMember);
        String expectedRequired = "Name";
        tokenizeAndAssertEqual(expectedRequired, actualRequired.toString());
        // if optional, get via dtor_value()
        MemberShape optionalField = structureShape.getMember("optionalString").get();
        CodeBlock actualOptional = underTest.getMemberFieldValue(optionalField);
        String expectedOptional = "OptionalString.dtor_value()";
        tokenizeAndAssertEqual(expectedOptional, actualOptional.toString());
    }

    @Test
    public void initTempArray() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        MemberShape enumListShape = structureShape.getMember("listEnum").get();
        CodeBlock actual = underTest.initTempArray(enumListShape);
        tokenizeAndAssertEqual(ToNativeConstants.INIT_TEMP_ARRAY, actual.toString());
    }

    @Test
    public void setMemberField() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        MemberShape stringMember = structureShape.getMember("name").get();
        CodeBlock actual = underTest.setMemberField(stringMember);
        String expected = "withName";
        tokenizeAndAssertEqual(expected, actual.toString());
    }

    @Test
    public void memberConversionMethodReference() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
        MemberShape stringMember = structureShape.getMember("name").get();
        MethodReference simpleActual = underTest.memberConversionMethodReference(stringMember);
        String simpleExpected = ToNativeConstants.STRING_CONVERSION;
        tokenizeAndAssertEqual(simpleExpected, simpleActual.asNormalReference().toString());
        // if in namespace reference created converter
        MemberShape enumMember = structureShape.getMember("keyUsage").get();
        MethodReference enumActual = underTest.memberConversionMethodReference(enumMember);
        String enumExpected = ToNativeConstants.KEY_USAGE_TYPE_CONVERSION;
        tokenizeAndAssertEqual(enumExpected, enumActual.asNormalReference().toString());
        // Otherwise, this target must be in another namespace
        MemberShape otherNamespaceMember = structureShape.getMember("otherNamespace").get();
        MethodReference otherNamespaceActual = underTest.memberConversionMethodReference(otherNamespaceMember);
        String otherNamespaceExpected = ToNativeConstants.OTHER_NAMESPACE_CONVERSION;
        tokenizeAndAssertEqual(otherNamespaceExpected, otherNamespaceActual.asNormalReference().toString());
    }

    @Test
    public void setWithConversionCall() {

    }

    @Test
    public void setWithConversionCallAndToArray() {
    }

    @Test
    public void generateConvertEnum() {
        ShapeId inputShapeId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageType");
        MethodSpec actual = underTest.generateConvertEnum(inputShapeId);
        String expected = KEY_USAGE_TYPE;
        tokenizeAndAssertEqual(expected, actual.toString());
    }

    @Test
    public void generateConvertString() {
        ShapeId plainStringShapeId = ShapeId.fromParts("com.amazonaws.kms", "TagKeyType");
        MethodSpec plainStringActual = underTest.generateConvertString(plainStringShapeId);
        assertNull(plainStringActual);
        ShapeId inputShapeId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageType");
        MethodSpec actual = underTest.generateConvertString(inputShapeId);
        String expected = KEY_USAGE_TYPE;
        tokenizeAndAssertEqual(expected, actual.toString());
    }
}
