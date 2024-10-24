// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import static software.amazon.smithy.utils.StringUtils.capitalize;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.WildcardTypeName;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;
import java.util.Objects;
import javax.annotation.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;

/**
 * Provides a consistent mapping between names of
 * model Shapes and generated identifiers in Java
 * for the Dafny generated Java code.
 */
public class Dafny extends NameResolver {

  @SuppressWarnings("unused")
  private static final Logger LOGGER = LoggerFactory.getLogger(Dafny.class);

  public static final Map<ShapeType, CodeBlock> TYPE_DESCRIPTOR_BY_SHAPE_TYPE;

  static {
    TYPE_DESCRIPTOR_BY_SHAPE_TYPE =
      Map.ofEntries(
        Map.entry(
          ShapeType.STRING,
          CodeBlock.of(
            "$T._typeDescriptor($T.CHAR)",
            Constants.DAFNY_SEQUENCE_CLASS_NAME,
            Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME
          )
        ),
        // Tony is not sure BLOB is correct...
        Map.entry(
          ShapeType.BLOB,
          CodeBlock.of(
            "$T._typeDescriptor($T.BYTE)",
            Constants.DAFNY_SEQUENCE_CLASS_NAME,
            Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME
          )
        ),
        Map.entry(
          ShapeType.BOOLEAN,
          CodeBlock.of("$T.BOOLEAN", Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME)
        ),
        Map.entry(
          ShapeType.BYTE,
          CodeBlock.of("$T.BYTE", Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME)
        ),
        Map.entry(
          ShapeType.SHORT,
          CodeBlock.of("$T.SHORT", Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME)
        ),
        Map.entry(
          ShapeType.INTEGER,
          CodeBlock.of("$T.INT", Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME)
        ),
        Map.entry(
          ShapeType.LONG,
          CodeBlock.of("$T.LONG", Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME)
        ),
        Map.entry(
          ShapeType.TIMESTAMP,
          CodeBlock.of(
            "$T._typeDescriptor($T.CHAR)",
            Constants.DAFNY_SEQUENCE_CLASS_NAME,
            Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME
          )
        ),
        Map.entry(
          ShapeType.BIG_INTEGER,
          CodeBlock.of(
            "$T.BIG_INTEGER",
            Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME
          )
        )
      );
  }

  private final DafnyVersion dafnyVersion;

  public Dafny(
    final String packageName,
    final Model model,
    final ServiceShape serviceShape,
    final CodegenSubject.AwsSdkVersion awsSdkVersion,
    final DafnyVersion dafnyVersion
  ) {
    super(
      packageName,
      serviceShape,
      model,
      modelPackageNameForServiceShape(serviceShape),
      awsSdkVersion
    );
    this.dafnyVersion = dafnyVersion;
  }

  /**
   * @param name A Constructor of the Dafny Datatype.
   * @param isRecordType Does the datatype have a single data constructor,
   *                     also called a "record type"?
   * @return The name of Dafny-Java created method to create an instance of
   * the constructor.
   */
  public static String datatypeConstructorCreate(
    String name,
    boolean isRecordType
  ) {
    if (isRecordType) {
      return "create";
    }
    return "create_" + DafnyNameResolverHelpers.dafnyCompilesExtra_(name);
  }

  //  Dafnys greater than or equal to this will need Type Descriptors for constructing datatypes
  private static final DafnyVersion NEEDS_TYPE_DESCRIPTORS_WHEN_CONSTRUCTING_DATATYPES =
    new DafnyVersion(4, 3, 0);

  /**
   * @return Whether the given Dafny version requires type descriptor values when instantiating datatype constructors.
   */
  public static boolean datatypeConstructorsNeedTypeDescriptors(
    DafnyVersion dafnyVersion
  ) {
    return (
      dafnyVersion.compareTo(
        NEEDS_TYPE_DESCRIPTORS_WHEN_CONSTRUCTING_DATATYPES
      ) >=
      0
    );
  }

  private boolean datatypeConstructorsNeedTypeDescriptors() {
    return datatypeConstructorsNeedTypeDescriptors(dafnyVersion);
  }

  /**
   * Code to create an instance of the None constructor of Wrappers.Option<T>.
   * @param typeDescriptor the code to create a TypeDescriptor for the type T,
   *                       which is needed if datatypeConstructorsNeedTypeDescriptors()
   */
  public CodeBlock createNone(CodeBlock typeDescriptor) {
    if (datatypeConstructorsNeedTypeDescriptors()) {
      return CodeBlock.of(
        "$T.create_None($L)",
        ClassName.get("Wrappers_Compile", "Option"),
        typeDescriptor
      );
    } else {
      return CodeBlock.of(
        "$T.create_None()",
        ClassName.get("Wrappers_Compile", "Option")
      );
    }
  }

  /**
   * Code to create an instance of the Some(value: T) constructor of Wrappers.Option<T>.
   * @param typeDescriptor the code to create a TypeDescriptor for the type T,
   *                       which is needed if datatypeConstructorsNeedTypeDescriptors()
   */
  public CodeBlock createSome(CodeBlock typeDescriptor, CodeBlock value) {
    if (datatypeConstructorsNeedTypeDescriptors()) {
      return CodeBlock.of(
        "$T.create_Some($L, $L)",
        Constants.DAFNY_OPTION_CLASS_NAME,
        typeDescriptor,
        value
      );
    } else {
      return CodeBlock.of(
        "$T.create_Some($L)",
        Constants.DAFNY_OPTION_CLASS_NAME,
        value
      );
    }
  }

  /**
   * Code to create an instance of the Success(value: T) constructor of Wrappers.Result<T, Error>.
   * @param valueTypeDescriptor the code to create a TypeDescriptor for the type T,
   *                       which is needed if datatypeConstructorsNeedTypeDescriptors()
   */
  public CodeBlock createSuccess(
    CodeBlock valueTypeDescriptor,
    CodeBlock value
  ) {
    if (datatypeConstructorsNeedTypeDescriptors()) {
      return CodeBlock.of(
        "$T.create_Success($L, Error._typeDescriptor(), $L)",
        Constants.DAFNY_RESULT_CLASS_NAME,
        valueTypeDescriptor,
        value
      );
    } else {
      return CodeBlock.of(
        "$T.create_Success($L)",
        Constants.DAFNY_RESULT_CLASS_NAME,
        value
      );
    }
  }

  /**
   * Code to create an instance of the Failure(error: Error) constructor of Wrappers.Result<T, Error>.
   * @param valueTypeDescriptor the code to create a TypeDescriptor for the type T,
   *                            which is needed if datatypeConstructorsNeedTypeDescriptors()
   */
  public CodeBlock createFailure(
    CodeBlock valueTypeDescriptor,
    CodeBlock error
  ) {
    if (datatypeConstructorsNeedTypeDescriptors()) {
      return CodeBlock.of(
        "$T.create_Failure($L, Error._typeDescriptor(), $L)",
        Constants.DAFNY_RESULT_CLASS_NAME,
        valueTypeDescriptor,
        error
      );
    } else {
      return CodeBlock.of(
        "$T.create_Failure($L)",
        Constants.DAFNY_RESULT_CLASS_NAME,
        error
      );
    }
  }

  public static String datatypeConstructorIs(String name) {
    String dafnyEnumName = DafnyNameResolverHelpers.dafnyCompilesExtra_(name);
    return "is_" + dafnyEnumName;
  }

  public static String datatypeDeconstructor(String name) {
    String dafnyEnumName = DafnyNameResolverHelpers.dafnyCompilesExtra_(name);
    return "dtor_" + dafnyEnumName + "()";
  }

  public static String aggregateSizeMethod(ShapeType shapeType) {
    return switch (shapeType) {
      case LIST -> "length()";
      case SET, MAP -> "size();";
      default -> throw new IllegalStateException(
        "aggregateSizeMethod only accepts LIST, SET, or MAP. Got : " + shapeType
      );
    };
  }

  static String modelPackageNameForNamespace(final String namespace) {
    return DafnyNameResolverHelpers.dafnyExternNamespaceForNamespace(namespace);
  }

  static String packageNameForServiceShape(ServiceShape serviceShape) {
    return DafnyNameResolverHelpers.packageNameForNamespace(
      serviceShape.getId().getNamespace()
    );
  }

  static String modelPackageNameForServiceShape(ServiceShape serviceShape) {
    return modelPackageNameForNamespace(serviceShape.getId().getNamespace());
  }

  public static CodeBlock getMemberField(MemberShape shape) {
    return CodeBlock.of("$L", datatypeDeconstructor(shape.getMemberName()));
  }

  /** If not optional, get via {@code dtor_<memberName>()}.
   * Otherwise, get via {@code dtor_<memberName>().dtor_value()}*/
  public static CodeBlock getMemberFieldValue(MemberShape shape) {
    // if required, get via Field
    if (shape.isRequired()) {
      return getMemberField(shape);
    }
    // if optional, get via dtor_value()
    return CodeBlock.of(
      "$L.$L",
      getMemberField(shape),
      datatypeDeconstructor("value")
    );
  }

  public static TypeName asDafnyResult(TypeName success, TypeName failure) {
    return ParameterizedTypeName.get(
      Constants.DAFNY_RESULT_CLASS_NAME,
      success,
      failure
    );
  }

  public static TypeName asDafnyOption(TypeName value) {
    return ParameterizedTypeName.get(Constants.DAFNY_OPTION_CLASS_NAME, value);
  }

  public String packageName() {
    return this.packageName;
  }

  /**
   * Returns the Dafny-compiled-Java type corresponding to the given shape.
   * <p>
   */
  @SuppressWarnings("OptionalGetWithoutIsPresent")
  public TypeName typeForShape(final ShapeId shapeId) {
    final Shape shape = model
      .getShape(shapeId)
      .orElseThrow(() ->
        new IllegalStateException("Cannot find shape " + shapeId)
      );
    return switch (shape.getType()) {
      case BLOB -> Dafny.typeForBlob();
      case BOOLEAN -> TypeName.BOOLEAN.box();
      case STRING -> typeForString(shape.asStringShape().get());
      case TIMESTAMP -> typeForCharacterSequence();
      case BYTE -> TypeName.BYTE.box();
      case SHORT -> TypeName.SHORT.box();
      case INTEGER -> TypeName.INT.box();
      case LONG -> TypeName.LONG.box();
      case DOUBLE -> Dafny.typeForDouble();
      case BIG_DECIMAL -> ClassName.get(BigDecimal.class);
      case BIG_INTEGER -> ClassName.get(BigInteger.class);
      case LIST, SET, MAP -> typeForAggregateWithWildcard(shapeId);
      case MEMBER -> typeForShape(shape.asMemberShape().get().getTarget());
      case STRUCTURE -> classForStructure(shape.asStructureShape().get());
      case SERVICE -> classNameForService(shape.asServiceShape().get());
      case RESOURCE -> classNameForResource(shape.asResourceShape().get());
      // Unions are identical to Structures (in this context).
      case UNION -> classForNotErrorNotUnitShape(shape.asUnionShape().get());
      case ENUM -> typeForString(shape.asStringShape().get());
      default -> throw new UnsupportedOperationException(
        "Unsupported shape " + shapeId
      );
    };
  }

  private static TypeName typeForBlob() {
    return ParameterizedTypeName.get(
      Constants.DAFNY_SEQUENCE_CLASS_NAME,
      WildcardTypeName.subtypeOf(TypeName.BYTE.box())
    );
  }

  static TypeName typeForDouble() {
    return typeForBlob();
  }

  @SuppressWarnings("OptionalGetWithoutIsPresent")
  public TypeName typeForAggregateWithWildcard(final ShapeId shapeId) {
    final Shape shape = model
      .getShape(shapeId)
      .orElseThrow(() ->
        new IllegalStateException("Cannot find shape " + shapeId)
      );

    if (
      !Generator.Constants.LIST_MAP_SET_SHAPE_TYPES.contains(shape.getType())
    ) {
      throw new UnsupportedOperationException(
        "No Dafny Java Type for %s yet.".formatted(shape.getType())
      );
    }
    return switch (shape.getType()) {
      case LIST -> ParameterizedTypeName.get(
        Constants.DAFNY_SEQUENCE_CLASS_NAME,
        WildcardTypeName.subtypeOf(
          typeForShape(shape.asListShape().get().getMember().getTarget())
        )
      );
      case SET -> ParameterizedTypeName.get(
        Constants.DAFNY_SET_CLASS_NAME,
        WildcardTypeName.subtypeOf(
          typeForShape(shape.asSetShape().get().getMember().getTarget())
        )
      );
      case MAP -> ParameterizedTypeName.get(
        Constants.DAFNY_MAP_CLASS_NAME,
        WildcardTypeName.subtypeOf(
          typeForShape(shape.asMapShape().get().getKey().getTarget())
        ),
        WildcardTypeName.subtypeOf(
          typeForShape(shape.asMapShape().get().getValue().getTarget())
        )
      );
      default -> throw new IllegalStateException(
        "Unexpected value: " + shape.getType()
      );
    };
  }

  public ClassName abstractClassForError() {
    return ClassName.get(modelPackage, "Error");
  }

  public ClassName classForOpaqueError() {
    return classForDatatypeConstructor("Error", "Opaque");
  }

  public CodeBlock typeDescriptor(ShapeId shapeId) {
    Shape shape = model
      .getShape(shapeId)
      .orElseThrow(() ->
        new IllegalStateException("Cannot find shape " + shapeId)
      );
    if (shape.isMemberShape()) {
      // We have just established it is a member shape, asMemberShape will return a value
      //noinspection OptionalGetWithoutIsPresent
      return typeDescriptor(shape.asMemberShape().get().getTarget());
    }
    if (shape.hasTrait(ErrorTrait.class)) {
      return CodeBlock.of(
        "$L()",
        new MethodReference(abstractClassForError(), "_typeDescriptor")
          .asNormalReference()
      );
    }
    if (
      shape.hasTrait(ReferenceTrait.class) ||
      shape.isServiceShape() ||
      shape.isResourceShape()
    ) {
      // It is safe to use typeForShape here, as ReferenceTrait will always turn into a Resource or Service
      TypeName interfaceClassName = typeForShape(shapeId);
      return CodeBlock.of(
        "$T.reference($T.class)",
        Constants.DAFNY_TYPE_DESCRIPTOR_CLASS_NAME,
        interfaceClassName
      );
    }
    if (shape.getId().equals(Constants.SMITHY_API_UNIT)) {
      return CodeBlock.of(
        "$L()",
        new MethodReference(
          Constants.DAFNY_TUPLE0_CLASS_NAME,
          "_typeDescriptor"
        )
          .asNormalReference()
      );
    }
    if (
      shape.getType().getCategory().equals(ShapeType.Category.SIMPLE) &&
      !shape.hasTrait(EnumTrait.class)
    ) {
      @Nullable
      CodeBlock typeDescriptor = shape.hasTrait(DafnyUtf8BytesTrait.class)
        // A Dafny UTF8 Bytes are basically a blob.
        // They are a sequence of uint8 in Dafny, this makes them the same as a Blob.
        ? TYPE_DESCRIPTOR_BY_SHAPE_TYPE.get(ShapeType.BLOB)
        : TYPE_DESCRIPTOR_BY_SHAPE_TYPE.get(shape.getType());
      if (Objects.nonNull(typeDescriptor)) {
        return CodeBlock.of("$L", typeDescriptor);
      }
    }
    if (shape.getType().isShapeType(ShapeType.LIST)) {
      CodeBlock elementTypeDescriptor = typeDescriptor(
        shape.asListShape().get().getMember().getTarget()
      );
      return CodeBlock.of(
        "$T._typeDescriptor($L)",
        Constants.DAFNY_SEQUENCE_CLASS_NAME,
        elementTypeDescriptor
      );
    }
    if (shape.getType().isShapeType(ShapeType.SET)) {
      CodeBlock elementTypeDescriptor = typeDescriptor(
        shape.asSetShape().get().getMember().getTarget()
      );
      return CodeBlock.of(
        "$T._typeDescriptor($L)",
        Constants.DAFNY_SET_CLASS_NAME,
        elementTypeDescriptor
      );
    }
    if (shape.getType().isShapeType(ShapeType.MAP)) {
      CodeBlock keyTypeDescriptor = typeDescriptor(
        shape.asMapShape().get().getKey().getTarget()
      );
      CodeBlock valueTypeDescriptor = typeDescriptor(
        shape.asMapShape().get().getValue().getTarget()
      );
      return CodeBlock.of(
        "$T._typeDescriptor($L, $L)",
        Constants.DAFNY_MAP_CLASS_NAME,
        keyTypeDescriptor,
        valueTypeDescriptor
      );
    }
    if (
      shape.getType().isShapeType(ShapeType.STRUCTURE) ||
      shape.getType().isShapeType(ShapeType.UNION) ||
      shape.getType().isShapeType(ShapeType.DOUBLE) ||
      shape.hasTrait(EnumTrait.class)
    ) {
      return CodeBlock.of(
        "$L()",
        new MethodReference(
          classForNotErrorNotUnitShape(shape),
          "_typeDescriptor"
        )
          .asNormalReference()
      );
    }
    throw new IllegalArgumentException(
      "Don't know how to create a type descriptor for this shape: %s".formatted(
          shape
        )
    );
  }

  /*
    For Datatypes, the destructor (thing) is the left Hand ,
    and the constructors (x, y) are the right hand of:
    datatype thing = x | y

    Outside the Dafny world,
    Datatype constructors are sometimes called variants.
    */
  public ClassName classForDatatypeConstructor(
    String dataTypeName,
    String constructorName
  ) {
    return ClassName.get(
      modelPackage,
      "%s_%s".formatted(
          DafnyNameResolverHelpers.dafnyCompilesExtra_(dataTypeName),
          DafnyNameResolverHelpers.dafnyCompilesExtra_(constructorName)
        )
    );
  }

  // This method assumes the shape is not an Error nor a Unit
  ClassName classForNotErrorNotUnitShape(Shape shape) {
    return classForNotErrorNotUnitShape(shape.toShapeId());
  }

  // This method assumes the shape is not an Error nor a Unit
  ClassName classForNotErrorNotUnitShape(ShapeId shapeId) {
    // Assume class will be in model package
    // i.e.: Dafny.<Namespace>.Types.Shape
    // And that Shape is not an Error
    return ClassName.get(
      modelPackageNameForNamespace(shapeId.getNamespace()),
      DafnyNameResolverHelpers.dafnyCompilesExtra_(
        capitalize(shapeId.getName())
      )
    );
  }

  TypeName typeForString(StringShape shape) {
    if (shape.hasTrait(EnumTrait.class)) {
      return classForNotErrorNotUnitShape(shape);
    }
    // If the shape has the dafnyUtf8Bytes trait,
    // the dafny representation will use Bytes
    if (shape.hasTrait(DafnyUtf8BytesTrait.class)) {
      return Dafny.typeForBlob();
    }
    return typeForCharacterSequence();
  }

  TypeName typeForCharacterSequence() {
    return ParameterizedTypeName.get(
      Constants.DAFNY_SEQUENCE_CLASS_NAME,
      WildcardTypeName.subtypeOf(Character.class)
    );
  }

  public TypeName classForStructure(StructureShape shape) {
    if (shape.hasTrait(ErrorTrait.class)) {
      return classForError(shape);
    }
    if (shape.hasTrait(ReferenceTrait.class)) {
      return typeForShape(
        shape.expectTrait(ReferenceTrait.class).getReferentId()
      );
    }
    if (shape.getId().equals(Constants.SMITHY_API_UNIT)) {
      return Constants.DAFNY_TUPLE0_CLASS_NAME;
    }
    return classForNotErrorNotUnitShape(shape);
  }

  public ClassName classForError(Shape shape) {
    if (!shape.hasTrait(ErrorTrait.class)) {
      throw new IllegalArgumentException(
        "shape MUST have ErrorTrait. ShapeId: %s".formatted(shape.getId())
      );
    }
    // AwsCryptographicMaterialProvidersException -> Error_AwsCryptographicMaterialProvidersException
    ClassName className = classForNotErrorNotUnitShape(shape);
    return ClassName.get(
      className.packageName(),
      "Error_" +
      DafnyNameResolverHelpers.dafnyCompilesExtra_(className.simpleName())
    );
  }

  /** @return The interface for a service client. */
  // This facilitates an override by a subclass
  ClassName classNameForService(final ServiceShape shape) {
    return interfaceForService(shape);
  }

  /** @return The interface for a service client.*/
  public static ClassName interfaceForService(final ServiceShape shape) {
    final String packageName =
      DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId(shape.getId());
    final String interfaceName = DafnyNameResolver.traitNameForServiceClient(
      shape
    );
    return ClassName.get(
      packageName,
      DafnyNameResolverHelpers.dafnyCompilesExtra_(interfaceName)
    );
  }

  /** @return The concrete class for a service client. */
  public ClassName classNameForConcreteServiceClient(ServiceShape shape) {
    String packageName = DafnyNameResolverHelpers.packageNameForNamespace(
      shape.getId().getNamespace()
    );
    String concreteClass = DafnyNameResolver.classNameForServiceClient(shape);
    return ClassName.get(
      packageName,
      DafnyNameResolverHelpers.dafnyCompilesExtra_(concreteClass)
    );
  }

  public ClassName classNameForNamespaceDefault() {
    String packageName = DafnyNameResolverHelpers.packageNameForNamespace(
      this.serviceShape.getId().getNamespace()
    );
    return ClassName.get(packageName, "__default");
  }

  /** @return The interface for a resource.*/
  // This facilitates an override by a subclass
  ClassName classNameForResource(final ResourceShape shape) {
    return Dafny.interfaceForResource(shape);
  }

  /** @return The interface for a resource.*/
  public static ClassName interfaceForResource(final ResourceShape shape) {
    final String packageName =
      DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId(shape.getId());
    final String interfaceName = DafnyNameResolver.traitNameForResource(shape);
    return ClassName.get(
      packageName,
      DafnyNameResolverHelpers.dafnyCompilesExtra_(interfaceName)
    );
  }

  public ClassName classNameForInterface(Shape shape) {
    // if shape is an AWS Service/Resource, return Dafny Types Interface
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.toShapeId())) {
      return classNameForAwsSdk(shape, this.awsSdkVersion);
    }
    // if operation takes a non-AWS Service/Resource, return Dafny Interface Or Local Service
    if (shape.isResourceShape()) {
      //noinspection OptionalGetWithoutIsPresent
      return interfaceForResource(shape.asResourceShape().get());
    }
    if (shape.isServiceShape()) {
      //noinspection OptionalGetWithoutIsPresent
      return interfaceForService(shape.asServiceShape().get());
    }
    throw new IllegalArgumentException(
      "Polymorph only supports interfaces for Service & Resource Shapes. ShapeId: %s".formatted(
          shape.toShapeId()
        )
    );
  }

  public static ClassName classNameForAwsSdk(
    Shape shape,
    CodegenSubject.AwsSdkVersion sdkVersion
  ) {
    if (shape.getType() != ShapeType.SERVICE) {
      throw new RuntimeException(
        "Polymorph only knows the class Name of Service clients. " +
        "Would a TypeName suffice? ShapeId: " +
        shape.toShapeId()
      );
    }
    @SuppressWarnings("OptionalGetWithoutIsPresent")
    ServiceShape service = shape.asServiceShape().get();
    return switch (sdkVersion) {
      case V1 -> AwsSdkDafnyV1.classNameForAwsService(service);
      case V2 -> AwsSdkDafnyV2.classNameForAwsService(service);
    };
  }
}
