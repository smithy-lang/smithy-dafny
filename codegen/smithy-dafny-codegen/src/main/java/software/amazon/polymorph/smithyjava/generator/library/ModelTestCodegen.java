package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.modeled.ModeledUnion;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.smoketests.traits.SmokeTestCase;
import software.amazon.smithy.smoketests.traits.SmokeTestsTrait;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PUBLIC;

public class ModelTestCodegen extends Generator {

    final JavaLibrary subject;

    public ModelTestCodegen(JavaLibrary subject) {
        super(subject);
        this.subject = subject;
    }

    @Override
    public Set<JavaFile> javaFiles() {
        LinkedHashSet<JavaFile> rtn = new LinkedHashSet<>();
        subject.model.getOperationShapesWithTrait(SmokeTestsTrait.class).stream()
                .map(this::smokeTestsClass)
                .forEachOrdered(c -> JavaFile.builder(subject.modelPackageName, c).build());
        return rtn;
    }

    private TypeSpec smokeTestsClass(OperationShape shape) {
        TypeSpec.Builder spec = TypeSpec
                .classBuilder(shape.getId().getName() + "SmokeTests")
                .addModifiers(PUBLIC, FINAL);
        SmokeTestsTrait smokeTests = shape.expectTrait(SmokeTestsTrait.class);
        smokeTests.getTestCases().stream()
                .map(this::smokeTest)
                .forEachOrdered(spec::addMethod);
        return spec.build();
    }

    private MethodSpec smokeTest(SmokeTestCase testCase) {
        return null;
    }
}
