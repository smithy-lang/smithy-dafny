package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.JavaFile;

import org.junit.Before;
import org.junit.Test;

import java.util.List;

import software.amazon.polymorph.smithyjava.ModelConstants;
import software.amazon.polymorph.smithyjava.generator.awssdk.TestSetupUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

public class ModelCodegenTest {
    protected ModelCodegen underTest;
    protected Model model;

    @Before
    public void setup() {
        model = TestSetupUtils.setupLocalModel(ModelConstants.CRYPTOGRAPHY_A_STRING_OPERATION);
        underTest = new ModelCodegen(TestSetupUtils.setupLibrary(model, "aws.cryptography.test"));
    }

    @Test
    public void ModeledErrorTest() {
        ShapeId structureId = ShapeId.fromParts("aws.cryptography.test", "TestError");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        JavaFile actual = underTest.modeledError(structureShape);
        String actualString = actual.toString();
        tokenizeAndAssertEqual(Constants.TEST_ERROR_EXPECTED, actualString);
    }

    @Test
    public void StructureWithRangeTraitTest() {
        ShapeId structureId = ShapeId.fromParts("aws.cryptography.test", "TestRangeMinMaxInteger");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        JavaFile actual = underTest.modeledStructure(structureShape);
        String actualString = actual.toString();
        int startBuildMethod = actualString.indexOf(Constants.RANGE_TRAIT_INTEGER_BUILD_METHOD_START);
        int endBuildMethod = actualString.indexOf(Constants.RANGE_TRAIT_INTEGER_BUILD_METHOD_RETURN)
                             + Constants.RANGE_TRAIT_INTEGER_BUILD_METHOD_RETURN.length()
                             + Constants.BUILD_METHOD_END_OFFSET;
        tokenizeAndAssertEqual(Constants.RANGE_TRAIT_INTEGER_BUILD_EXPECTED,
                actualString.substring(startBuildMethod, endBuildMethod));
    }

    @Test
    public void StructureWithLengthTraitTest() {
        ShapeId structureId = ShapeId.fromParts("aws.cryptography.test", "TestLengthMinMaxBlob");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        JavaFile actual = underTest.modeledStructure(structureShape);
        String actualString = actual.toString();
        int startBuildMethod = actualString.indexOf(Constants.LENGTH_TRAIT_BLOB_BUILD_METHOD_START);
        int endBuildMethod = actualString.indexOf(Constants.LENGTH_TRAIT_BLOB_BUILD_METHOD_RETURN)
                             + Constants.LENGTH_TRAIT_BLOB_BUILD_METHOD_RETURN.length()
                             + Constants.BUILD_METHOD_END_OFFSET;
        tokenizeAndAssertEqual(Constants.LENGTH_TRAIT_BLOB_BUILD_METHOD_EXPECTED,
                actualString.substring(startBuildMethod, endBuildMethod));
    }

    // TODO: Test structure with Enum member

}
