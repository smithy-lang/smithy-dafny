// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library;

import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;
import com.squareup.javapoet.WildcardTypeName;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.generator.ToDafny;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StructureShape;

/**
 * ToDafnyLibrary generates ToDafny,
 * a helper class for the Java Library's Shim.<p>
 * ToDafny holds methods to convert Native Java types to Dafny Java types.<p>
 * As such,
 * ToDafnyLibrary holds the logic to generate these methods based on:
 * <ul>
 *     <li>a smithy model</li>
 *     <li>knowledge of how smithy-dafny generates Dafny</li>
 *     <li>knowledge of how Dafny compiles Java</li>
 *     <li>knowledge of how smithy-java Library generates Java</li>
 * </ul>
 */
public class ToDafnyLibrary extends ToDafny {

  static final MethodReference DAFNY_UTF8_BYTES = new MethodReference(
    COMMON_TO_DAFNY_SIMPLE,
    "DafnyUtf8Bytes"
  );
  // Hack to override CodegenSubject
  // See code comment on ModelCodegen for details.
  final JavaLibrary subject;

  public static ClassName className(JavaLibrary javaLibrary) {
    return ClassName.get(javaLibrary.packageName, TO_DAFNY);
  }

  public ToDafnyLibrary(JavaLibrary javaLibrary) {
    super(javaLibrary, className(javaLibrary));
    this.subject = javaLibrary;
  }

  @Override
  public Set<JavaFile> javaFiles() {
    JavaFile.Builder builder = JavaFile.builder(
      thisClassName.packageName(),
      toDafny()
    );
    return Collections.singleton(builder.build());
  }

  TypeSpec toDafny() {
    ArrayList<MethodSpec> toDafnyMethods = new ArrayList<>();
    // NativeError (really, any Error in the service)
    toDafnyMethods.add(runtimeException());
    // OpaqueError
    toDafnyMethods.add(opaqueError());
    // CollectionError
    toDafnyMethods.add(collectionError());
    // Structures
    subject
      .getStructuresInServiceNamespace()
      .stream()
      .map(this::modeledStructure)
      .forEachOrdered(toDafnyMethods::add);
    // Modeled exception classes
    subject
      .getErrorsInServiceNamespace()
      .stream()
      .map(this::modeledError)
      .forEachOrdered(toDafnyMethods::add);
    // Enums
    subject
      .getEnumsInServiceNamespace()
      .stream()
      .map(this::modeledEnum)
      .forEachOrdered(toDafnyMethods::add);
    // Unions
    subject
      .getUnionsInServiceNamespace()
      .stream()
      .map(this::modeledUnion)
      .forEachOrdered(toDafnyMethods::add);
    // Lists
    subject
      .getListsInServiceNamespace()
      .stream()
      .map(this::modeledList)
      .forEachOrdered(toDafnyMethods::add);
    // Sets
    subject
      .getSetsInServiceNamespace()
      .stream()
      .map(this::modeledSet)
      .forEachOrdered(toDafnyMethods::add);
    // Maps
    subject
      .getMapsInServiceNamespace()
      .stream()
      .map(this::modeledMap)
      .forEachOrdered(toDafnyMethods::add);
    // Resources
    subject
      .getResourcesInServiceNamespace()
      .stream()
      .map(this::modeledResource)
      .forEachOrdered(toDafnyMethods::add);
    // The Service, it's self
    toDafnyMethods.add(modeledService(subject.serviceShape));
    return TypeSpec
      .classBuilder(thisClassName)
      .addModifiers(Modifier.PUBLIC)
      .addMethods(toDafnyMethods)
      .build();
  }

  // Converts any subclass of RuntimeException to the correct Dafny Error,
  // or casts it as an OpaqueError.
  MethodSpec runtimeException() {
    TypeName dafnyError = subject.dafnyNameResolver.abstractClassForError();
    ClassName runtimeException = ClassName.get(RuntimeException.class);
    MethodSpec.Builder method = MethodSpec
      .methodBuilder("Error")
      .returns(dafnyError)
      .addModifiers(PUBLIC_STATIC)
      .addParameter(runtimeException, VAR_INPUT);
    List<ClassName> allNativeErrors = subject
      .getErrorsInServiceNamespace()
      .stream()
      .map(subject.nativeNameResolver::classNameForStructure)
      .collect(Collectors.toCollection(ArrayList::new));
    allNativeErrors.add(
      OpaqueError.nativeClassName(subject.nativeNameResolver.modelPackage)
    );
    allNativeErrors.add(
      CollectionOfErrors.nativeClassName(
        subject.nativeNameResolver.modelPackage
      )
    );
    allNativeErrors.forEach(errorClassName ->
      method
        .beginControlFlow("if ($L instanceof $T)", VAR_INPUT, errorClassName)
        .addStatement(
          "return $T.Error(($T) $L)",
          thisClassName,
          errorClassName,
          VAR_INPUT
        )
        .endControlFlow()
    );
    return method
      .addStatement("return $T.create_Opaque($L)", dafnyError, VAR_INPUT)
      .build();
  }

  MethodSpec opaqueError() {
    TypeName dafnyError = subject.dafnyNameResolver.abstractClassForError();
    ClassName opaqueError = OpaqueError.nativeClassName(
      subject.nativeNameResolver.modelPackage
    );
    return MethodSpec
      .methodBuilder("Error")
      .returns(dafnyError)
      .addModifiers(PUBLIC_STATIC)
      .addParameter(opaqueError, VAR_INPUT)
      .addStatement("return $T.create_Opaque($L.obj())", dafnyError, VAR_INPUT)
      .build();
  }

  MethodSpec collectionError() {
    ClassName dafnyError = subject.dafnyNameResolver.abstractClassForError();
    ClassName nativeError = CollectionOfErrors.nativeClassName(
      subject.nativeNameResolver.modelPackage
    );
    ParameterizedTypeName listType = ParameterizedTypeName.get(
      software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_SEQUENCE_CLASS_NAME,
      WildcardTypeName.subtypeOf(dafnyError)
    );
    CodeBlock listConverter = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE
      .get(ShapeType.LIST)
      .asNormalReference();
    MethodReference errorTypeDescriptor = new MethodReference(
      dafnyError,
      "_typeDescriptor"
    );
    TypeName messageType = subject.dafnyNameResolver.typeForShape(
      ShapeId.fromParts("smithy.api", "String")
    );
    CodeBlock messageConverter = SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
      .get(ShapeType.STRING)
      .asNormalReference();
    return MethodSpec
      .methodBuilder("Error")
      .returns(dafnyError)
      .addModifiers(PUBLIC_STATIC)
      .addParameter(nativeError, VAR_INPUT)
      .addStatement(
        "$T list = $L(\n$L.list(), \n$T::Error, \n$L())",
        listType,
        listConverter,
        VAR_INPUT,
        thisClassName,
        errorTypeDescriptor.asNormalReference()
      )
      .addStatement(
        "$T message = $L($L.getMessage())",
        messageType,
        messageConverter,
        VAR_INPUT
      )
      .addStatement(
        "return $T.create_CollectionOfErrors(list, message)",
        dafnyError
      )
      .build();
  }

  @Override
  protected MethodSpec modeledStructure(final StructureShape structureShape) {
    if (structureShape.hasTrait(PositionalTrait.class)) {
      return positionalStructure(structureShape);
    }
    return super.modeledStructure(structureShape);
  }

  protected MethodSpec positionalStructure(StructureShape shape) {
    final MemberShape onlyMember = PositionalTrait.onlyMember(shape);
    final ShapeId onlyMemberId = onlyMember.toShapeId();
    final String methodName = capitalize(shape.getId().getName());
    final TypeName inputType = subject.nativeNameResolver.typeForShape(
      onlyMemberId
    );
    final TypeName outputType = subject.dafnyNameResolver.typeForShape(
      onlyMemberId
    );
    MethodSpec.Builder builder = MethodSpec
      .methodBuilder(methodName)
      .addModifiers(PUBLIC_STATIC)
      .returns(outputType)
      .addParameter(inputType, VAR_INPUT);
    CodeBlock variable = CodeBlock.of(
      "$L",
      uncapitalize(onlyMember.getMemberName())
    );
    builder.addStatement(memberDeclaration(onlyMember, variable));
    builder.addStatement(
      memberConvertAndAssign(
        onlyMember,
        variable,
        CodeBlock.of("$L", VAR_INPUT)
      )
    );
    builder.addStatement("return $L", variable);
    return builder.build();
  }

  protected MethodSpec modeledResource(ResourceShape shape) {
    final String methodName = capitalize(shape.getId().getName());
    return MethodSpec
      .methodBuilder(methodName)
      .addModifiers(PUBLIC_STATIC)
      .returns(Dafny.interfaceForResource(shape))
      .addParameter(Native.classNameForResourceInterface(shape), VAR_INPUT)
      .addStatement(
        "return $L.impl()",
        subject.wrapWithShim(shape.getId(), CodeBlock.of(VAR_INPUT))
      )
      .build();
  }

  protected MethodSpec modeledService(ServiceShape shape) {
    final String methodName = capitalize(shape.getId().getName());
    return MethodSpec
      .methodBuilder(methodName)
      .addModifiers(PUBLIC_STATIC)
      .returns(Dafny.interfaceForService(shape))
      .addParameter(
        Native.classNameForInterfaceOrLocalService(shape, subject.sdkVersion),
        VAR_INPUT
      )
      .addStatement("return $L.impl()", CodeBlock.of(VAR_INPUT))
      .build();
  }

  /** For Library structure members, the getter is `un-capitalized member name`. */
  @Override
  protected CodeBlock getMember(
    CodeBlock variableName,
    MemberShape memberShape
  ) {
    return CodeBlock.of("$L.$L()", variableName, memberShape.getMemberName());
  }

  // Reference & Positional often mask Service or Resource shapes
  // that can be in other namespaces.
  // This override simplifies their lookup.
  @Override
  public MethodReference conversionMethodReference(Shape shape) {
    ModelUtils.ResolvedShapeId resolvedShapeId = ModelUtils.resolveShape(
      shape.getId(),
      subject.model
    );
    Shape resolvedShape = subject.model.expectShape(
      resolvedShapeId.resolvedId()
    );
    if (resolvedShape.isServiceShape() || resolvedShape.isResourceShape()) {
      return super.nonSimpleConversionMethodReference(resolvedShape);
    }
    // If the target has the dafnyUtf8Bytes trait,
    // going to Dafny, the Strings need to be converted to Bytes
    if (resolvedShape.hasTrait(DafnyUtf8BytesTrait.class)) {
      return DAFNY_UTF8_BYTES;
    }
    return super.conversionMethodReference(shape);
  }
}
