// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import java.util.Set;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.utils.StringUtils;

@SuppressWarnings("OptionalGetWithoutIsPresent")
public class ToDafnyTest {

  protected ToDafnyTestImpl underTest;
  protected Model model;

  static class ToDafnyTestImpl extends ToDafny {

    public ToDafnyTestImpl(CodegenSubject subject) {
      super(
        subject,
        ClassName.get(subject.dafnyNameResolver.packageName(), TO_DAFNY)
      );
    }

    /** For AWS SDK structure members, the getter is `get + capitalized member name`. */
    @Override //At least for now, we are just going to use AWS SDK V1 style getter's here
    protected CodeBlock getMember(
      CodeBlock variableName,
      MemberShape memberShape
    ) {
      return CodeBlock.of(
        "$L.get$L()",
        variableName,
        StringUtils.capitalize(memberShape.getMemberName())
      );
    }

    @Override
    public Set<JavaFile> javaFiles() {
      return null;
    }
  }
  /*@Before
    public void setup() {
        model = TestSetupUtils.setupTwoLocalModel(ModelConstants.KMS_KITCHEN, ModelConstants.OTHER_NAMESPACE);
        underTest  = new ToDafnyTestImpl(TestSetupUtils.setupAwsSdkV1(model, "kms"));
    }

    @Test
    public void modeledStructure() {
        // structureShape.members().size() == 0
        ShapeId simpleId = ShapeId.fromParts("com.amazonaws.kms", "Simple");
        final StructureShape simpleShape = model.expectShape(simpleId, StructureShape.class);
        MethodSpec simpleActual = underTest.modeledStructure(simpleShape);
        String simpleExpected = ToDafnyConstants.SIMPLE_STRUCTURE;
        tokenizeAndAssertEqual(simpleExpected, simpleActual.toString());
        // structureShape.members().size() != 0
        ShapeId aOptionalId = ShapeId.fromParts("com.amazonaws.kms", "AOptional");
        final StructureShape optionalShape = model.expectShape(aOptionalId, StructureShape.class);
        MethodSpec aOptionalActual = underTest.modeledStructure(optionalShape);
        tokenizeAndAssertEqual(ToDafnyConstants.A_OPTIONAL_STRUCTURE, aOptionalActual.toString());
    }

    @Test
    public void memberDeclaration() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        // if required
        MemberShape memberRequired = structureShape.getMember("name").get();
        CodeBlock actualRequired = underTest.memberDeclaration(memberRequired, CodeBlock.of("name"));
        String expectedRequired = ToDafnyConstants.MEMBER_DECLARATION_REQUIRED;
        tokenizeAndAssertEqual(expectedRequired, actualRequired.toString());
        // optional
        MemberShape memberOptional = structureShape.getMember("message").get();
        CodeBlock actualOptional = underTest.memberDeclaration(memberOptional, CodeBlock.of("message"));
        String expectedOptional = ToDafnyConstants.MEMBER_DECLARATION_OPTIONAL;
        tokenizeAndAssertEqual(expectedOptional, actualOptional.toString());
    }

    @Test
    public void memberAssignment() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        // if required
        MemberShape memberRequired = structureShape.getMember("name").get();
        CodeBlock actualRequired = underTest.memberConvertAndAssign(
                memberRequired, CodeBlock.of("name"), CodeBlock.of("nativeValue.getName()"));
        String expectedRequired = ToDafnyConstants.MEMBER_ASSIGNMENT_REQUIRED;
        tokenizeAndAssertEqual(expectedRequired, actualRequired.toString());
        // if optional
        MemberShape memberOptional = structureShape.getMember("message").get();
        CodeBlock actualOptional = underTest.memberConvertAndAssign(
                memberOptional, CodeBlock.of("message"), CodeBlock.of("nativeValue.getMessage()"));
        String expectedOptional = ToDafnyConstants.MEMBER_ASSIGNMENT_OPTIONAL;
        tokenizeAndAssertEqual(expectedOptional, actualOptional.toString());
    }

    @Test
    public void memberConversionMethodReference() {
        ShapeId structureId = ShapeId.fromParts("com.amazonaws.kms", "Kitchen");
        StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
        // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
        MemberShape stringMember = structureShape.getMember("name").get();
        MethodReference simpleActual = underTest.conversionMethodReference(model.expectShape(stringMember.getTarget()));
        String simpleExpected = ToDafnyConstants.STRING_CONVERSION;
        tokenizeAndAssertEqual(simpleExpected, simpleActual.asNormalReference().toString());
        // if in namespace reference created converter
        MemberShape enumMember = structureShape.getMember("keyUsage").get();
        MethodReference enumActual = underTest.conversionMethodReference(model.expectShape(enumMember.getTarget()));
        String enumExpected = ToDafnyConstants.KEY_USAGE_TYPE_CONVERSION;
        String enumString = enumActual.asNormalReference().toString();
        tokenizeAndAssertEqual(enumExpected, enumString);
        // Otherwise, this target must be in another namespace
        MemberShape otherNamespaceMember = structureShape.getMember("otherNamespace").get();
        MethodReference otherNamespaceActual = underTest.conversionMethodReference(model.expectShape(otherNamespaceMember.getTarget()));
        String otherNamespaceExpected = ToDafnyConstants.OTHER_NAMESPACE_CONVERSION;
        String otherNamespaceString = otherNamespaceActual.asNormalReference().toString();
        tokenizeAndAssertEqual(otherNamespaceExpected, otherNamespaceString);
    }

    @Test
    public void modeledError() {
        Model localModel = TestSetupUtils.setupLocalModel(ModelConstants.KMS_A_STRING_OPERATION);
        ToDafnyTestImpl localUnderTest = new ToDafnyTestImpl(TestSetupUtils.setupAwsSdkV1(localModel, "kms"));
        ShapeId errorId = ShapeId.fromParts("com.amazonaws.kms", "DependencyTimeoutException");
        StructureShape errorShape = localModel.expectShape(errorId, StructureShape.class);
        MethodSpec errorActual = localUnderTest.modeledError(errorShape);
        String errorExpected = ToDafnyConstants.GENERATE_CONVERT_ERROR;
        tokenizeAndAssertEqual(errorExpected, errorActual.toString());
    }*/
}
