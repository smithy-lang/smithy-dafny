package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.modeled.ModeledUnion;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.node.NumberNode;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.node.StringNode;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.NumberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.smoketests.traits.SmokeTestCase;
import software.amazon.smithy.smoketests.traits.SmokeTestsTrait;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
                .forEachOrdered(rtn::add);
        return rtn;
    }

    private JavaFile smokeTestsClass(OperationShape shape) {
        TypeSpec.Builder spec = TypeSpec
                .classBuilder(shape.getId().getName() + "SmokeTests")
                .addModifiers(PUBLIC, FINAL);
        SmokeTestsTrait smokeTests = shape.expectTrait(SmokeTestsTrait.class);
        smokeTests.getTestCases().stream()
                .map(testCase -> smokeTest(shape, testCase))
                .forEachOrdered(spec::addMethod);
        TypeSpec classType = spec.build();
        return JavaFile.builder(subject.modelPackageName, classType).build();
    }

    private MethodSpec smokeTest(final OperationShape operationShape, SmokeTestCase testCase) {

        // TODO: escape all names properly
        final String methodName = testCase.getId();
        MethodSpec.Builder method = MethodSpec
                .methodBuilder(methodName)
                .addAnnotation(Constants.JUPITER_TEST)
                .addModifiers(PUBLIC)
                .returns(TypeName.VOID);

        final TypeName clientType = subject.nativeNameResolver.typeForShape(subject.serviceShape.toShapeId());
        final String operationName = operationShape.toShapeId().getName();
        final ShapeId configShapeId = subject.serviceShape.expectTrait(LocalServiceTrait.class).getConfigId();
        final TypeName configType = subject.nativeNameResolver.typeForShape(configShapeId);

        // SimpleConstraintsConfig config = SimpleConstraintsConfig.builder().build();
        // SimpleConstraints client = SimpleConstraints.builder()
        //         .SimpleConstraintsConfig(config)
        //         .build();
        method.addStatement("$T config = $T.builder().build()", configType, configType);
        method.addStatement("$T client = $T.builder().$L(config).build()", clientType, clientType, configShapeId.getName());

        // GetConstraintsInput inputBuilder = GetConstraintsInput.builder();
        // ...
        // (multiple calls to populate builder)
        // ...
        // GetConstraintsInput input = inputBuilder.build();
        // TODO: error handling
        Shape inputShape = subject.model.expectShape(operationShape.getInput().get());
        declareModeledValue(method, "input", inputShape, testCase.getParams().get());

        // client.GetConstraints(input);
        // TODO: or assertThrows(...)
        method.addStatement("client.$L(input)", operationName);

        return method.build();
    }

    private void declareModeledValue(MethodSpec.Builder method, String variableName, Shape shape, Node value) {
        switch (shape.getType()) {
            case STRUCTURE -> declareStructureValue(method, variableName, (StructureShape)shape, (ObjectNode)value);
            case STRING -> declareStringValue(method, variableName, (StringShape) shape, (StringNode)value);
            case INTEGER -> declareNumberValue(method, variableName, (NumberShape) shape, (NumberNode) value);
            default -> throw new IllegalArgumentException("Node values of this shape type not yet supported: " + shape);
        }
    }

    private void declareStructureValue(MethodSpec.Builder method, String variableName, StructureShape structureShape, ObjectNode value) {
        final TypeName inputType = subject.nativeNameResolver.typeForShape(structureShape.getId());
        final TypeName inputBuilderType = BuilderSpecs.builderInterfaceName((ClassName)inputType);

        method.addStatement("$T $LBuilder = $T.builder()", inputBuilderType, variableName, inputType);

        for (Map.Entry<String, Node> entry : value.getStringMap().entrySet()) {
            String memberName = entry.getKey();
            Node memberValue = entry.getValue();
            MemberShape memberShape = structureShape.getAllMembers().get(memberName);
            Shape targetShape = subject.model.expectShape(memberShape.getTarget());
            declareModeledValue(method, memberName, targetShape, memberValue);
            // TODO: name munging
            method.addStatement("$LBuilder.$L($L)", variableName, memberName, memberName);
        }

        method.addStatement("$T $L = inputBuilder.build()", inputType, variableName);
    }

    private void declareStringValue(MethodSpec.Builder method, String variableName, StringShape stringShape, StringNode value) {
        // TODO: escaping
        method.addStatement("String $L = \"$L\"", variableName, value.getValue());
    }

    private void declareNumberValue(MethodSpec.Builder method, String variableName, NumberShape numberShape, NumberNode value) {
        TypeName typeName = subject.nativeNameResolver.typeForShape(numberShape.getId());
        method.addStatement("$T $L = $L", typeName, variableName, value.getValue());
    }
}
