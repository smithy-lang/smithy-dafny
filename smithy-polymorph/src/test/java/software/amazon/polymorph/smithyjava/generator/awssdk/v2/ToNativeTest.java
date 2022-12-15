package software.amazon.polymorph.smithyjava.generator.awssdk.V2;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;

import org.junit.Before;
import org.junit.Test;

import java.nio.file.Path;
import java.util.Map;
import java.util.Set;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.ModelConstants;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.SetShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertThrows;
import static software.amazon.polymorph.smithyjava.generator.awssdk.ToNativeConstants.KEY_USAGE_TYPE;
import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

@SuppressWarnings("OptionalGetWithoutIsPresent")
public class ToNativeTest {
    // Why two underTests?
    // As we refactor ToNativeAwsV2 and abstract ToNative,
    // we are going to bump into permission issues in unit tests
    // for protected methods.
    // ToNativeTestImpl exposes the abstract classes protected methods
    // to this test class,
    // b/c ToNativeTestImpl is defined INSIDE the test class.
    // But we still need to test the yet to be refactored logic.
    // TODO: Clean up this test class by creating test class for ToNativeAwsV2
    // and moving AwsV2 specific tests there.
    protected ToNativeAwsV2 underTest;
    protected ToNativeTestImpl underTestAbstract;
    protected Model model;

    static class ToNativeTestImpl extends ToNativeAwsV2 {

        public ToNativeTestImpl(JavaAwsSdkV2 awsSdk) {
            super(awsSdk);
        }

        @Override
        public Set<JavaFile> javaFiles() {
            return null;
        }

        @Override
        // This allows the test class to call the otherwise protected method.
        protected MethodSpec modeledList(ListShape shape) {
            return super.modeledList(shape);
        }

        @Override
        // This allows the test class to call the otherwise protected method.
        protected MethodSpec modeledSet(SetShape shape) {
            return super.modeledSet(shape);
        }

        @Override
        // This allows the test class to call the otherwise protected method.
        protected MethodSpec modeledMap(MapShape shape) { return super.modeledMap(shape);}

        @Override
        // This allows the test class to call the otherwise protected method.
        protected MethodReference memberConversionMethodReference(MemberShape memberShape) {
            return super.memberConversionMethodReference(memberShape);
        }

        @Override
        // This allows the test class to call the otherwise protected method.
        protected CodeBlock setWithConversionCall(MemberShape member, CodeBlock getMember) {
            return super.setWithConversionCall(member, getMember);
        }
    }

    @Before
    public void setup() {
        model = TestSetupUtils.setupTwoLocalModel(ModelConstants.KMS_KITCHEN, ModelConstants.OTHER_NAMESPACE);
        underTest  = new ToNativeAwsV2(TestSetupUtils.setupAwsSdk(model, "kms"));
        underTestAbstract  = new ToNativeTestImpl(TestSetupUtils.setupAwsSdk(model, "kms"));
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
    public void initTempArray() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        MemberShape enumListShape = structureShape.getMember("listEnum").get();
        CodeBlock actual = underTest.initTempArray(enumListShape);
        tokenizeAndAssertEqual(ToNativeConstants.INIT_TEMP_ARRAY, actual.toString());
    }

    @Test
    public void memberConversionMethodReference() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
        MemberShape stringMember = structureShape.getMember("name").get();
        MethodReference simpleActual = underTestAbstract.memberConversionMethodReference(stringMember);
        String simpleExpected = ToNativeConstants.STRING_CONVERSION;
        tokenizeAndAssertEqual(simpleExpected, simpleActual.asNormalReference().toString());
        // if in namespace reference created converter
        MemberShape enumMember = structureShape.getMember("keyUsage").get();
        MethodReference enumActual = underTestAbstract.memberConversionMethodReference(enumMember);
        String enumExpected = ToNativeConstants.KEY_USAGE_TYPE_CONVERSION;
        tokenizeAndAssertEqual(enumExpected, enumActual.asNormalReference().toString());
        // Otherwise, this target must be in another namespace
        MemberShape otherNamespaceMember = structureShape.getMember("otherNamespace").get();
        MethodReference otherNamespaceActual = underTestAbstract.memberConversionMethodReference(otherNamespaceMember);
        String otherNamespaceExpected = ToNativeConstants.OTHER_NAMESPACE_CONVERSION;
        tokenizeAndAssertEqual(otherNamespaceExpected, otherNamespaceActual.asNormalReference().toString());
    }

    @Test
    public void setWithConversionCall() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        MemberShape ciphertextMember = structureShape.getMember("ciphertext").get();
        CodeBlock actual = underTestAbstract.setWithConversionCall(ciphertextMember, Dafny.getMemberFieldValue(ciphertextMember));
        tokenizeAndAssertEqual(ToNativeConstants.SET_WITH_CONVERSION_CALL, actual.toString());
    }

    @Test
    public void setWithConversionCallAndToArray() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        MemberShape enumListShape = structureShape.getMember("listEnum").get();
        CodeBlock actual = underTest.setWithConversionCallAndToArray(enumListShape);
        tokenizeAndAssertEqual(ToNativeConstants.SET_WITH_CONVERSION_CALL_AND_TO_ARRAY, actual.toString());
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

    @Test
    public void generateConvertList() {
        ShapeId listId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageTypes");
        ListShape listShape = model.expectShape(listId, ListShape.class);
        MethodSpec listActual = underTestAbstract.modeledList(listShape);
        tokenizeAndAssertEqual(ToNativeConstants.GENERATE_CONVERT_LIST, listActual.toString());
    }

    @Test
    public void generateConvertSet() {
        ShapeId setId = ShapeId.fromParts("com.amazonaws.kms", "Names");
        SetShape setShape = model.expectShape(setId, SetShape.class);
        MethodSpec setActual = underTestAbstract.modeledSet(setShape);
        tokenizeAndAssertEqual(ToNativeConstants.GENERATE_CONVERT_SET, setActual.toString());
    }

    @Test
    public void generateConvertMap() {
        ShapeId mapId = ShapeId.fromParts("com.amazonaws.kms", "EncryptionContextType");
        MapShape mapShape = model.expectShape(mapId, MapShape.class);
        MethodSpec mapActual = underTestAbstract.modeledMap(mapShape);
        tokenizeAndAssertEqual(ToNativeConstants.GENERATE_CONVERT_MAP, mapActual.toString());
    }

    @Test
    public void generateConvertStructure() {
        // structureShape.members().size() == 0
        ShapeId simpleId = ShapeId.fromParts("com.amazonaws.kms", "Simple");
        StructureShape simpleShape = model.expectShape(simpleId, StructureShape.class);
        MethodSpec simpleActual = underTest.modeledStructure(simpleShape);
        tokenizeAndAssertEqual(ToNativeConstants.SIMPLE_STRUCTURE, simpleActual.toString());
        // if optional, check if present
        ShapeId aOptionalId = ShapeId.fromParts("com.amazonaws.kms", "AOptional");
        MethodSpec aOptionalActual = underTest.generateConvert(aOptionalId);
        tokenizeAndAssertEqual(ToNativeConstants.A_OPTIONAL_STRUCTURE, aOptionalActual.toString());
        // if converting a LIST or SET of enums
        ShapeId requiredListEnumId = ShapeId.fromParts("com.amazonaws.kms", "RequiredListEnum");
        MethodSpec requiredListEnumActual = underTest.generateConvert(requiredListEnumId);
        tokenizeAndAssertEqual(ToNativeConstants.REQUIRED_LIST_ENUM_STRUCTURE, requiredListEnumActual.toString());
    }

    @Test
    public void generateConvert() {
        // case Simple
        ShapeId CiphertextTypeId = ShapeId.fromParts("com.amazonaws.kms", "CiphertextType");
        assertNull(underTest.generateConvert(CiphertextTypeId));
        // case ENUM
        ShapeId enumId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageType");
        tokenizeAndAssertEqual(KEY_USAGE_TYPE, underTest.generateConvert(enumId).toString());
        // case LIST
        ShapeId listId = ShapeId.fromParts("com.amazonaws.kms", "KeyUsageTypes");
        tokenizeAndAssertEqual(ToNativeConstants.GENERATE_CONVERT_LIST, underTest.generateConvert(listId).toString());
        // case SET
        ShapeId setId = ShapeId.fromParts("com.amazonaws.kms", "Names");
        tokenizeAndAssertEqual(ToNativeConstants.GENERATE_CONVERT_SET, underTest.generateConvert(setId).toString());
        // case MAP
        ShapeId mapId = ShapeId.fromParts("com.amazonaws.kms", "EncryptionContextType");
        tokenizeAndAssertEqual(ToNativeConstants.GENERATE_CONVERT_MAP, underTest.generateConvert(mapId).toString());
        // case STRUCTURE
        ShapeId simpleId = ShapeId.fromParts("com.amazonaws.kms", "Simple");
        tokenizeAndAssertEqual(ToNativeConstants.SIMPLE_STRUCTURE, underTest.generateConvert(simpleId).toString());
        // default
        ShapeId doubleId = ShapeId.fromParts("com.amazonaws.kms", "NotSupported");
        assertThrows(UnsupportedOperationException.class, () -> underTest.generateConvert(doubleId));
    }

    @Test
    public void generate() {
        Model model = TestSetupUtils.setupLocalModel(ModelConstants.KMS_A_STRING_OPERATION);
        ToNativeAwsV2 underTest = new ToNativeAwsV2(TestSetupUtils.setupAwsSdk(model, "kms"));
        final Map<Path, TokenTree> actual = underTest.generate();
        final Path expectedPath = Path.of("Dafny/Com/Amazonaws/Kms/ToNative.java");
        Path[] temp = new Path[1];
        final Path actualPath = actual.keySet().toArray(temp)[0];
        assertEquals(expectedPath, actualPath);
        final String actualSource = actual.get(actualPath).toString();
        tokenizeAndAssertEqual(ToNativeConstants.KMS_A_STRING_OPERATION_JAVA_FILE, actualSource);
    }
}
