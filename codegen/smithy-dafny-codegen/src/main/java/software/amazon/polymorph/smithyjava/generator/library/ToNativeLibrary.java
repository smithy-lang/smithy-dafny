// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library;

import static software.amazon.polymorph.smithyjava.nameresolver.Dafny.datatypeConstructorIs;
import static software.amazon.polymorph.smithyjava.nameresolver.Dafny.datatypeDeconstructor;
import static software.amazon.smithy.utils.StringUtils.capitalize;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.generator.ToNative;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
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
 * ToNativeLibrary generates ToNative,
 * a helper class for the Java Library's Shim.<p>
 * ToNative holds methods to convert Dafny Java types to Native Java types.<p>
 * As such,
 * ToNativeLibrary holds the logic to generate these methods based on:
 * <ul>
 *     <li>a smithy model</li>
 *     <li>knowledge of how smithy-dafny generates Dafny</li>
 *     <li>knowledge of how Dafny compiles Java</li>
 *     <li>knowledge of how smithy-java Library generates Java</li>
 * </ul>
 */
public class ToNativeLibrary extends ToNative {

  static final MethodReference DAFNY_UTF8_BYTES = new MethodReference(
    COMMON_TO_NATIVE_SIMPLE,
    "DafnyUtf8Bytes"
  );
  // Hack to override CodegenSubject
  // See code comment on ModelCodegen for details.
  final JavaLibrary subject;

  public static ClassName className(JavaLibrary javaLibrary) {
    return ClassName.get(javaLibrary.packageName, TO_NATIVE);
  }

  public ToNativeLibrary(JavaLibrary javaLibrary) {
    super(javaLibrary, className(javaLibrary));
    this.subject = javaLibrary;
  }

  @Override
  public Set<JavaFile> javaFiles() {
    JavaFile.Builder builder = JavaFile.builder(
      thisClassName.packageName(),
      toNative()
    );
    return Collections.singleton(builder.build());
  }

  TypeSpec toNative() {
    ArrayList<MethodSpec> toNativeMethods = new ArrayList<>();
    // OpaqueError
    toNativeMethods.add(opaqueError());
    // CollectionError
    toNativeMethods.add(collectionError());
    // Modeled exception classes
    subject
      .getErrorsInServiceNamespace()
      .stream()
      .map(this::modeledError)
      .forEachOrdered(toNativeMethods::add);
    // Any Error
    toNativeMethods.add(dafnyError());
    // Structures
    subject
      .getStructuresInServiceNamespace()
      .stream()
      .map(this::modeledStructure)
      .forEachOrdered(toNativeMethods::add);
    // Enums
    subject
      .getEnumsInServiceNamespace()
      .stream()
      .map(this::modeledEnum)
      .forEachOrdered(toNativeMethods::add);
    // Unions
    subject
      .getUnionsInServiceNamespace()
      .stream()
      .map(this::modeledUnion)
      .forEachOrdered(toNativeMethods::add);
    // Lists
    subject
      .getListsInServiceNamespace()
      .stream()
      .map(this::modeledList)
      .forEachOrdered(toNativeMethods::add);
    // Sets
    subject
      .getSetsInServiceNamespace()
      .stream()
      .map(this::modeledSet)
      .forEachOrdered(toNativeMethods::add);
    // Maps
    subject
      .getMapsInServiceNamespace()
      .stream()
      .map(this::modeledMap)
      .forEachOrdered(toNativeMethods::add);
    // Resources
    subject
      .getResourcesInServiceNamespace()
      .stream()
      .map(this::modeledResource)
      .forEachOrdered(toNativeMethods::add);
    // The Service, it's self
    toNativeMethods.add(modeledService(subject.serviceShape));
    return TypeSpec
      .classBuilder(thisClassName)
      .addModifiers(Modifier.PUBLIC)
      .addMethods(toNativeMethods)
      .build();
  }

  MethodSpec opaqueError() {
    ClassName inputType = subject.dafnyNameResolver.classForDatatypeConstructor(
      "Error",
      "Opaque"
    );
    ClassName returnType = OpaqueError.nativeClassName(
      subject.modelPackageName
    );
    MethodSpec.Builder method = super.initializeErrorMethodSpec(
      inputType,
      returnType
    );
    method = super.createNativeBuilder(method, returnType);
    // Set Value
    method.addStatement(
      "$L.obj($L.$L)",
      NATIVE_BUILDER,
      VAR_INPUT,
      datatypeDeconstructor("obj")
    );
    // Build and Return
    return super.buildAndReturn(method);
  }

  MethodSpec collectionError() {
    ClassName inputType = subject.dafnyNameResolver.classForDatatypeConstructor(
      "Error",
      "CollectionOfErrors"
    );
    ClassName returnType = CollectionOfErrors.nativeClassName(
      subject.modelPackageName
    );
    CodeBlock listConverter = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE
      .get(ShapeType.LIST)
      .asNormalReference();
    CodeBlock messageConverter = SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
      .get(ShapeType.STRING)
      .asNormalReference();
    MethodSpec.Builder method = super.initializeErrorMethodSpec(
      inputType,
      returnType
    );
    super.createNativeBuilder(method, returnType);
    // Set Values
    method
      .addStatement(
        "$L.list(\n$L(\n$L.$L, \n$T::Error))",
        NATIVE_BUILDER,
        listConverter,
        VAR_INPUT,
        datatypeDeconstructor("list"),
        thisClassName
      )
      .addStatement(
        "$L.message($L($L.$L))",
        NATIVE_BUILDER,
        messageConverter,
        VAR_INPUT,
        datatypeDeconstructor("message")
      );
    // Build and Return
    return super.buildAndReturn(method);
  }

  MethodSpec dafnyError() {
    ClassName inputType = subject.dafnyNameResolver.abstractClassForError();
    ClassName returnType = ClassName.get(RuntimeException.class);
    MethodSpec.Builder method = super.initializeErrorMethodSpec(
      inputType,
      returnType
    );
    // We need a list of `<datatypeConstructor>`.
    // We have the logic exposed to look up the ClassName,
    // which, as a string, will be <modelPackage>.Error_<datatypeConstructor>.
    // We get the "simpleName" (i.e.: Error_<datatypeConstructor>),
    // and, finally, replace "Error_" with nothing, thus getting just "<datatypeConstructor>".
    List<String> allDafnyErrorConstructors = subject
      .getErrorsInServiceNamespace()
      .stream()
      .map(subject.dafnyNameResolver::classForError)
      .map(ClassName::simpleName)
      .map(simpleName -> simpleName.replaceFirst("Error_", ""))
      .collect(Collectors.toCollection(ArrayList::new)); // We need a mutable list, so we can't use stream().toList()
    allDafnyErrorConstructors.add("Opaque");
    allDafnyErrorConstructors.add("CollectionOfErrors");
    allDafnyErrorConstructors.forEach(constructorName ->
      method
        .beginControlFlow(
          "if ($L.$L())",
          VAR_INPUT,
          datatypeConstructorIs(constructorName)
        )
        .addStatement(
          "return $T.Error(($T) $L)",
          thisClassName,
          subject.dafnyNameResolver.classForDatatypeConstructor(
            "Error",
            constructorName
          ),
          VAR_INPUT
        )
        .endControlFlow()
    );
    // Handle Errors from another service:
    LocalServiceTrait localServiceTrait = subject.serviceShape.expectTrait(
      LocalServiceTrait.class
    );
    if (localServiceTrait.getDependencies() != null) {
      localServiceTrait
        .getDependencies()
        .stream()
        .map(subject.model::expectShape)
        .map(Shape::asServiceShape)
        .filter(Optional::isPresent)
        .map(Optional::get)
        .forEach(serviceShape -> {
          String serviceName = DafnyNameResolver.moduleNamespace(
            serviceShape.toShapeId().getNamespace()
          );
          method
            .beginControlFlow(
              "if ($L.$L())",
              VAR_INPUT,
              datatypeConstructorIs(serviceName)
            )
            .addStatement(
              "return $T.Error($L.$L)",
              ToNative.ToNativeClassNameForShape(
                serviceShape,
                subject.sdkVersion
              ),
              VAR_INPUT,
              datatypeDeconstructor(serviceName)
            )
            .endControlFlow();
        });
    }
    // If the Error cannot be placed into any of the above, call it opaque and move on
    super.createNativeBuilder(
      method,
      OpaqueError.nativeClassName(subject.modelPackageName)
    );
    method.addStatement("$L.obj($L)", NATIVE_BUILDER, VAR_INPUT);
    return super.buildAndReturn(method);
  }

  @Override
  protected MethodSpec modeledStructure(StructureShape structureShape) {
    if (structureShape.hasTrait(PositionalTrait.class)) {
      return positionalStructure(structureShape);
    }
    // if this structure does NOT have a positional trait,
    // then we can use the abstract's modeledStructure.
    return super.modeledStructure(structureShape);
  }

  protected MethodSpec positionalStructure(StructureShape structureShape) {
    final MemberShape onlyMember = PositionalTrait.onlyMember(structureShape);
    final ShapeId onlyMemberId = onlyMember.toShapeId();
    final String methodName = capitalize(structureShape.getId().getName());
    final TypeName inputType = subject.dafnyNameResolver.typeForShape(
      onlyMemberId
    );
    final TypeName returnType = subject.nativeNameResolver.typeForShape(
      onlyMemberId
    );
    MethodSpec.Builder method = initializeMethodSpec(
      methodName,
      inputType,
      returnType
    );

    // Optional and Positional are a weird combo,
    // particularly in Java,
    // for now, a non-set optional will return null

    if (onlyMember.isOptional()) {
      // if optional, check if present
      method.beginControlFlow("if ($L.is_Some())", VAR_INPUT);
    }
    // return result of conversion call of member
    method.addStatement(returnWithConversionCall(onlyMember));
    if (onlyMember.isOptional()) {
      method.endControlFlow();
      // else, optional is empty, return null
      method.addStatement(returnNull());
    }
    return method.build();
  }

  protected MethodSpec modeledResource(ResourceShape shape) {
    final String methodName = capitalize(shape.getId().getName());
    MethodSpec.Builder method = MethodSpec
      .methodBuilder(methodName)
      .addModifiers(PUBLIC_STATIC)
      .addParameter(Dafny.interfaceForResource(shape), VAR_INPUT)
      .returns(
        Native.classNameForInterfaceOrLocalService(shape, subject.sdkVersion)
      );

    if (shape.hasTrait(ExtendableTrait.class)) {
      method
        .beginControlFlow(
          "if ($L instanceof $T.NativeWrapper)",
          VAR_INPUT,
          subject.nativeNameResolver.classNameForResource(shape)
        )
        .addStatement(
          "return (($T.NativeWrapper) $L)._impl",
          subject.nativeNameResolver.classNameForResource(shape),
          VAR_INPUT
        )
        .endControlFlow();
    }
    return method
      .addStatement(
        "return $L",
        subject.wrapWithShim(shape.getId(), CodeBlock.of(VAR_INPUT))
      )
      .build();
  }

  protected MethodSpec modeledService(ServiceShape shape) {
    final String methodName = capitalize(shape.getId().getName());
    final ClassName serviceClass = Native.classNameForInterfaceOrLocalService(
      shape,
      subject.sdkVersion
    );
    return MethodSpec
      .methodBuilder(methodName)
      .addModifiers(PUBLIC_STATIC)
      .returns(serviceClass)
      .addParameter(Dafny.interfaceForService(shape), VAR_INPUT)
      .addStatement("return new $T($L)", serviceClass, CodeBlock.of(VAR_INPUT))
      .build();
  }

  protected CodeBlock returnWithConversionCall(final MemberShape shape) {
    CodeBlock memberConversionMethod = conversionMethodReference(
      subject.model.expectShape(shape.getTarget())
    )
      .asNormalReference();
    return CodeBlock.of("return $L($L)", memberConversionMethod, VAR_INPUT);
  }

  protected static CodeBlock returnNull() {
    return CodeBlock.of("return null");
  }

  // Reference & Positional often mask Service or Resource shapes
  // that can be in other namespaces.
  // This override simplifies their lookup.
  @Override
  public MethodReference conversionMethodReference(Shape shape) {
    ModelUtils.ResolvedShapeId resolvedShapeId = ModelUtils.resolveShape(
      shape.toShapeId(),
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
    return super.conversionMethodReference(resolvedShape);
  }
}
