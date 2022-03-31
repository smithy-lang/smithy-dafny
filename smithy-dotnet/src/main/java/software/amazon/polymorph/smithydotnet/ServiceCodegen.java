// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import com.google.common.annotations.VisibleForTesting;

import software.amazon.polymorph.smithydotnet.nativeWrapper.NativeWrapperCodegen;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.EntityShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.TraitDefinition;

import java.nio.file.Path;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Stream;

/**
 * Codegen for a service's API skeleton (service interface and structures).
 *
 * Note: this code generator does not aim to generate "nicely-formatted" code. That responsibility is left to external code formatters.
 */
public class ServiceCodegen {
    private final Model model;
    private final ServiceShape serviceShape;
    private final DotNetNameResolver nameResolver;

    public ServiceCodegen(final Model model, final ShapeId serviceShapeId) {
        this.model = model;

        this.serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);
        this.nameResolver = new DotNetNameResolver(model, serviceShape);
    }

    // TODO: get smarter about imports. maybe just fully qualify all model-agnostic types?
    private final static List<String> UNCONDITIONAL_IMPORTS = List.of(
            "System",
            "AWS.EncryptionSDK.Core"
    );

    /**
     * @return map of skeleton's file paths to generated ASTs
     */
    public Map<Path, TokenTree> generate() {
        final Map<Path, TokenTree> codeByPath = new HashMap<>();

        // Use LinkedHashSet to dedupe while maintaining insertion order
        final LinkedHashSet<String> importNamespaces = new LinkedHashSet<>(UNCONDITIONAL_IMPORTS);
        importNamespaces.add(nameResolver.namespaceForService());
        final TokenTree prelude = TokenTree.of(
                importNamespaces.stream().map("using %s;"::formatted).map(Token::of)
        ).lineSeparated();

        // Common exception class
        final Path commonExceptionPath = Path.of(String.format("%s.cs", nameResolver.classForCommonServiceException()));
        final TokenTree commonExceptionPathCode = generateCommonExceptionClass();
        codeByPath.put(commonExceptionPath, commonExceptionPathCode.prepend(prelude));

        // Specific exception classes
        model.getStructureShapes()
                .stream()
                .filter(shape -> shape.hasTrait(ErrorTrait.class))
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), serviceShape))
                .forEach(shape -> {
                    final Path exceptionClassPath = Path.of(String.format("%s.cs", nameResolver.classForSpecificServiceException(shape.getId())));
                    final TokenTree exceptionClass = generateSpecificExceptionClass(shape);
                    codeByPath.put(exceptionClassPath, exceptionClass.prepend(prelude));
                });

        // Structures
        model.getStructureShapes()
                .stream()
                .filter(this::shouldGenerateStructure)
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), serviceShape))
                .forEach(shape -> {
                    final Path structureClassPath = Path.of(String.format("%s.cs", nameResolver.classForStructure(shape.getId())));
                    final TokenTree structureCode = generateStructureClass(shape);
                    codeByPath.put(structureClassPath, structureCode.prepend(prelude));
                });

        // Enums
        model.getStringShapesWithTrait(EnumTrait.class)
                .stream()
                .map(Shape::getId)
                .filter(enumShapeId -> ModelUtils.isInServiceNamespace(enumShapeId, serviceShape))
                .forEach(enumShapeId -> {
                    final Path enumClassPath = Path.of(String.format("%s.cs", nameResolver.classForEnum(enumShapeId)));
                    final TokenTree enumCode = generateEnumClass(enumShapeId);
                    codeByPath.put(enumClassPath, enumCode.prepend(prelude));
                });

        // Resources
        model.getResourceShapes()
                .stream()
                .map(ResourceShape::getId)
                .filter(resourceShapeId -> ModelUtils.isInServiceNamespace(resourceShapeId, serviceShape))
                .forEach(resourceShapeId -> {
                    final Path resourceInterfacePath = Path.of(String.format("%s.cs", nameResolver.interfaceForResource(resourceShapeId)));
                    final TokenTree resourceInterface = generateResourceInterface(resourceShapeId);
                    codeByPath.put(resourceInterfacePath, resourceInterface.prepend(prelude));

                    final Path resourceClassPath = Path.of(String.format("%s.cs", nameResolver.baseClassForResource(resourceShapeId)));
                    final TokenTree resourceClass = generateResourceClass(resourceShapeId);
                    codeByPath.put(resourceClassPath, resourceClass.prepend(prelude));

                    if (shouldGenerateNativeWrapper(resourceShapeId)) {
                        final NativeWrapperCodegen nativeWrapperCodegen = new NativeWrapperCodegen(
                                model, serviceShape.getId(), resourceShapeId, nameResolver);
                        final Path nativeWrapperPath = Path.of(
                                String.format("%s.cs",
                                        nameResolver.nativeWrapperClassForResource(
                                                resourceShapeId)));
                        final TokenTree nativeWrapperClass = nativeWrapperCodegen.generate();
                        codeByPath.put(nativeWrapperPath, nativeWrapperClass);
                    }
                });
        return codeByPath;
    }

    boolean shouldGenerateNativeWrapper(ShapeId shapeId) {
        ResourceShape resourceShape = model.expectShape(shapeId, ResourceShape.class);
        return resourceShape.hasTrait(ExtendableTrait.class);
    }

    @VisibleForTesting
    boolean shouldGenerateStructure(final StructureShape structureShape) {
        return
                // Traits are structures, but aren't needed outside Smithy
                !structureShape.hasTrait(TraitDefinition.class)
                // References are transparent in C#, so we don't need to generate a class for them
                && !structureShape.hasTrait(ReferenceTrait.class)
                // Structures marked with positional are intended to be unwrapped, so we don't need
                // to generate the wrapper structure
                && !structureShape.hasTrait(PositionalTrait.class)
                // We generate exception classes (instead of typical data classes) for error structures
                && !structureShape.hasTrait(ErrorTrait.class);
    }

    /**
     * Generates the signature of a method
     *   e.g. EncryptOutput Encrypt ( EncryptInput input )
     * Extracted into its own method because we want to generate this both for the interface and for the base class
     *
     * NOTE: The return has no modifiers or access level. If callers need to set a method as public/protected/etc,
     *  they are responsible for doing so.
     */
    public TokenTree generateOperationSignature(final ShapeId operationShapeId) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        final TokenTree outputType = generateOperationReturnType(operationShape);
        final TokenTree paramTokens = generateOperationParameter(operationShape);

        return TokenTree.of(
                outputType,
                Token.of(nameResolver.methodForOperation(operationShapeId)),
                paramTokens.parenthesized()
        );

    }

    public TokenTree generateInterfaceMethod(final ShapeId operationShapeId) {
        // For interfaces (which don't have bodies for operations), we just take the basic operation
        // and end the statement with a ';'
        return TokenTree.of(
                generateOperationSignature(operationShapeId),
                Token.of(';')
        );
    }

    /**
     * @return a common exception class for this service, from which all other service exception classes extend
     */
    public TokenTree generateCommonExceptionClass() {
        final String exceptionName = nameResolver.classForCommonServiceException();

        final TokenTree classHeader = Token.of("public class %s : Exception".formatted(exceptionName));
        final TokenTree emptyCtor = Token.of("public %s() : base() {}".formatted(exceptionName));
        final TokenTree messageCtor = Token.of("public %s(string message) : base(message) {}".formatted(exceptionName));
        final TokenTree classBody = TokenTree.of(emptyCtor, messageCtor);
        return TokenTree.of(classHeader, classBody.braced()).namespaced(Token.of(nameResolver.namespaceForService()));
    }

    /**
     * @return an exception class for the given error structure shape, which extends from the common exception class
     */
    public TokenTree generateSpecificExceptionClass(final StructureShape structureShape) {
        ModelUtils.validateErrorStructure(structureShape);

        final String commonExceptionName = nameResolver.classForCommonServiceException();
        final String exceptionName = nameResolver.classForSpecificServiceException(structureShape.getId());

        final TokenTree classHeader = Token.of("public class %s : %s".formatted(exceptionName, commonExceptionName));
        final TokenTree messageCtor = Token.of("public %s(string message) : base(message) {}".formatted(exceptionName));
        return TokenTree.of(classHeader, messageCtor.braced()).namespaced(Token.of(nameResolver.namespaceForService()));
    }

    /**
     * @return a data class for the given structure shape
     */
    public TokenTree generateStructureClass(final StructureShape structureShape) {
        final Token structureClassName = Token.of(nameResolver.classForStructure(structureShape.getId()));

        final TokenTree fields = TokenTree.of(ModelUtils.streamStructureMembers(structureShape)
                .map(this::generateStructureClassField)).lineSeparated();
        final TokenTree properties = TokenTree.of(ModelUtils.streamStructureMembers(structureShape)
                .map(this::generateStructureClassProperty)).lineSeparated();
        final TokenTree validateMethod = generateStructureValidateMethod(structureShape);
        final TokenTree bodyTokens = TokenTree.of(fields, properties, validateMethod).lineSeparated().braced();

        final TokenTree namespace = Token.of(nameResolver.namespaceForService());
        return TokenTree.of(Token.of("public class"), structureClassName, bodyTokens).namespaced(namespace);
    }

    /**
     * @return field declaration for the given structure member
     */
    public TokenTree generateStructureClassField(final MemberShape memberShape) {
        final TokenTree typeToken = Token.of(nameResolver.classFieldTypeForStructureMember(memberShape));
        return TokenTree.of(
                Token.of("private"),
                typeToken,
                Token.of(nameResolver.classFieldForStructureMember(memberShape)),
                Token.of(';'));
    }

    /**
     * @return property for the given structure member, with a getter, setter, and IsSet for valueTypes
     */
    public TokenTree generateStructureClassProperty(final MemberShape memberShape) {
        final String fieldName = nameResolver.classFieldForStructureMember(memberShape);

        // Class fields are always nullable, so we need to provide a default value for value types
        final boolean isValueType = nameResolver.isValueType(memberShape.getTarget());
        final String unwrapValue = isValueType ? ".GetValueOrDefault()" : "";

        final TokenTree getter = Token.of("get { return this.%s%s; }".formatted(fieldName, unwrapValue));
        final TokenTree setter = Token.of("set { this.%s = value; }".formatted(fieldName));

        final String type = nameResolver.classPropertyTypeForStructureMember(memberShape);
        final String propertyName = nameResolver.classPropertyForStructureMember(memberShape);
        final TokenTree body = TokenTree.of(getter, setter).lineSeparated();
        final TokenTree accessors = TokenTree.of("public", type, propertyName).append(body.braced());
        return TokenTree.of(accessors, generateIsSetStructureClassProperty(memberShape)).lineSeparated();
    }

    /**
     * @return IsSet method for either reference types or value types
     */
    private TokenTree generateIsSetStructureClassProperty(final MemberShape memberShape) {
        final String methodName = nameResolver.isSetMethodForStructureMember(memberShape);
        TokenTree body;
        if (nameResolver.isValueType(memberShape.getTarget())) {
            body = TokenTree.of("return this.%s.HasValue;".formatted(
                    nameResolver.classFieldForStructureMember(memberShape)));
        } else {
            body = TokenTree.of("return this.%s != null;".formatted(
                    nameResolver.classFieldForStructureMember(memberShape)));
        }
        return TokenTree.of("internal bool", methodName, "()").append(body.braced());
    }

    /**
     * Generates a validation method for structures. Note that not all Smithy constraint traits are supported.
     * <p>
     * Supported constraint traits:
     * <ul>
     *     <li>{@code @required}</li>
     * </ul>
     * TODO:
     * <ul>
     *     <li>{@code @range}</li>
     *     <li>{@code @length}</li>
     * </ul>
     *
     * @return Validate() method for generated structure classes
     */
    private TokenTree generateStructureValidateMethod(final StructureShape structureShape) {
        final Token signature = Token.of("public void Validate()");
        final TokenTree checks = TokenTree.of(structureShape.members().stream()
                .filter(MemberShape::isRequired)
                .map(memberShape -> {
                    final String isSetMethod = nameResolver.isSetMethodForStructureMember(memberShape);
                    final String propertyName = nameResolver.classPropertyForStructureMember(memberShape);
                    return Token.of("""
                            if (!%s()) throw new System.ArgumentException("Missing value for required property '%s'");
                            """.formatted(isSetMethod, propertyName));
                })).braced();

        return TokenTree.of(signature, checks);
    }

    public TokenTree generateResourceInterface(final ShapeId resourceShapeId) {
        final ResourceShape resourceShape = model.expectShape(resourceShapeId, ResourceShape.class);

        final TokenTree bodyTokens = TokenTree.of(
                resourceShape.getOperations().stream().map(
                        operationShapeId -> generateInterfaceMethod(operationShapeId)
                )).lineSeparated();

        return TokenTree.of(
                Token.of("public interface"),
                Token.of(nameResolver.interfaceForResource(resourceShapeId)),
                bodyTokens.braced()
        ).namespaced(Token.of(nameResolver.namespaceForService()));
    }

    /**
     * Takes a resource or service shape and generates the body of an abstract base class which implements operations
     * and declares abstract operations which should be overridden.
     *
     * @param entityShapeId The id of the service or resource shape
     * @return A token tree with the class body
     */
    public TokenTree generateEntityClassBody(final ShapeId entityShapeId) {
        final EntityShape entityShape = model.expectShape(entityShapeId, EntityShape.class);

        final TokenTree bodyTokens = TokenTree.of(entityShape.getOperations().stream().map(operationShapeId -> {
            final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

            final TokenTree concreteMethodSignature = TokenTree.of(
                    TokenTree.of("public"),
                    generateOperationSignature(operationShapeId)
            );

            final TokenTree returnType = generateOperationReturnType(operationShape);
            final TokenTree param = generateOperationParameter(operationShape);
            final Token abstractMethodName = Token.of(nameResolver.abstractMethodForOperation(operationShapeId));

            final Token validate = Token.of(operationShape.getInput().isPresent() ? "input.Validate();" : "");
            final Token abstractArg = Token.of(operationShape.getInput().isPresent() ? "input" : "");
            final Token returnOrBlank = Token.of(operationShape.getOutput().isPresent() ? "return" : "");
            final TokenTree concreteMethodBody = TokenTree.of(
                    validate,
                    returnOrBlank, abstractMethodName, abstractArg.parenthesized(), Token.of(';')
            ).braced();

            final TokenTree abstractMethodSignature = TokenTree.of(
                    Token.of("protected abstract"),
                    returnType,
                    abstractMethodName,
                    param.parenthesized(),
                    Token.of(';')
            );

            return TokenTree.of(concreteMethodSignature, concreteMethodBody, abstractMethodSignature).lineSeparated();
        })).lineSeparated();

        return bodyTokens;
    }

    public TokenTree generateResourceClass(final ShapeId resourceShapeId) {
        final TokenTree bodyTokens = generateEntityClassBody(resourceShapeId);

        final TokenTree classDeclaration = TokenTree.of(
                "public abstract class",
                nameResolver.baseClassForResource(resourceShapeId),
                ":",
                nameResolver.interfaceForResource(resourceShapeId)
        );
        return classDeclaration
                .append(bodyTokens.braced())
                .namespaced(Token.of(nameResolver.namespaceForService()));
    }

    /**
     * @return either "OperationInput input" if the given operation shape has input OperationInput, or "" otherwise
     */
    public TokenTree generateOperationParameter(final OperationShape operationShape) {
        return operationShape.getInput()
                .map(inputShapeId -> TokenTree.of(nameResolver.baseTypeForShape(inputShapeId), "input"))
                .orElse(TokenTree.empty());
    }

    /**
     * @return either "OperationOutput" if the given operation shape has output OperationOutput, or "void" otherwise
     */
    public TokenTree generateOperationReturnType(final OperationShape operationShape) {
        return operationShape.getOutput()
                .map(outputShapeId -> Token.of(nameResolver.baseTypeForShape(outputShapeId)))
                .orElse(Token.of("void"));
    }

    private EnumTrait getAndValidateEnumTrait(final StringShape stringShape) {
        final EnumTrait enumTrait = stringShape.getTrait(EnumTrait.class)
                .orElseThrow(() -> new IllegalStateException("EnumTrait absent on provided string shape"));
        if (enumTrait.hasNames() && hasInvalidEnumNames(enumTrait)) {
            throw new IllegalStateException("Enum definition names must be uppercase alphanumeric and begin with a letter");
        }
        if (!enumTrait.hasNames() && hasInvalidMembersForUnnamedEnum(enumTrait)) {
            throw new IllegalStateException("Unnamed enum definitions cannot have documentation or tags, and can't be deprecated");
        }
        return enumTrait;
    }

    /**
     * Note:
     * - we don't currently do anything with tags
     * - doc comments aren't generated for unnamed enum variants
     *
     * @return a class containing constants for the enum members
     */
    public TokenTree generateEnumClass(final ShapeId stringShapeId) {
        final StringShape stringShape = model.expectShape(stringShapeId, StringShape.class);
        final EnumTrait enumTrait = getAndValidateEnumTrait(stringShape);

        final String enumClassName = nameResolver.classForEnum(stringShapeId);
        final String enumValueTypeName = enumTrait.hasNames() ? enumClassName : "string";
        final TokenTree namedEnumValues = enumTrait.hasNames()
                ? generateNamedEnumValues(enumTrait, enumClassName)
                : TokenTree.empty();
        final TokenTree enumValuesArray = generateEnumValuesArray(enumTrait, enumValueTypeName);

        // For enums, the constructor does nothing except extend the parent ConstantClass constructor
        final TokenTree constructor = TokenTree.of(
                "public",
                enumClassName,
                "(string value)",
                ": base(value)",
                "{}"
        );

        final TokenTree classBody = TokenTree.of(
                namedEnumValues,
                enumValuesArray,
                constructor
        ).lineSeparated().braced();

        final TokenTree constantClassImport = enumTrait.hasNames() ? Token.of("using Amazon.Runtime;") : TokenTree.empty();
        final TokenTree extendsConstantClass = enumTrait.hasNames() ? Token.of(": ConstantClass") : TokenTree.empty();

        return TokenTree.of(
                constantClassImport,
                Token.of("public class"),
                Token.of(enumClassName),
                extendsConstantClass,
                classBody
        ).namespaced(Token.of(nameResolver.namespaceForService()));
    }

    private boolean hasInvalidEnumNames(final EnumTrait enumTrait) {
        return !enumTrait.getValues().stream()
                .map(EnumDefinition::getName)
                .map(Optional::get)
                .allMatch(ModelUtils::isValidEnumDefinitionName);
    }

    private boolean hasInvalidMembersForUnnamedEnum(final EnumTrait enumTrait) {
        return enumTrait.getValues()
                .stream()
                .anyMatch(enumDefinition ->
                        enumDefinition.getDocumentation().isPresent()
                        || !enumDefinition.getTags().isEmpty()
                        || enumDefinition.isDeprecated()
                );
    }

    private TokenTree generateNamedEnumValues(final EnumTrait enumTrait, final String enumClassName) {
        return TokenTree.of(enumTrait.getValues().stream().map(enumDefinition -> {
            assert enumDefinition.getName().isPresent();
            final String definitionName = enumDefinition.getName().get();

            final TokenTree docComment = enumDefinition.getDocumentation()
                    .map(this::formatDocComment)
                    .orElse(TokenTree.empty());
            final TokenTree obsoleteAnnotation = enumDefinition.isDeprecated()
                    ? Token.of("[System.Obsolete]")
                    : TokenTree.empty();
            final TokenTree constDefinition = TokenTree.of(
                    "public static readonly",
                    enumClassName,
                    definitionName,
                    "= new",
                    enumClassName,
                    String.format("(\"%s\");", enumDefinition.getValue())
            );

            return TokenTree.of(docComment, obsoleteAnnotation, constDefinition).lineSeparated();
        }));
    }

    private TokenTree generateEnumValuesArray(final EnumTrait enumTrait, final String valueTypeName) {
        final Stream<TokenTree> valueStrings;
        if (enumTrait.hasNames()) {
            valueStrings = enumTrait.getValues()
                    .stream()
                    .map(EnumDefinition::getName)
                    .map(Optional::get)
                    .sorted()  // Sort values for sane diffs
                    .map(Token::of);
        } else {
            valueStrings = enumTrait.getEnumDefinitionValues()
                    .stream()
                    .sorted()  // Sort values for sane diffs
                    .map(value -> Token.of(String.format("\"%s\"", value)));
        }
        final TokenTree valuesArrayLiteral = TokenTree.of(valueStrings).separated(Token.of(",")).braced();
        return TokenTree.of(
                Token.of("public static readonly "),
                Token.of(valueTypeName),
                Token.of("[] Values = "),
                valuesArrayLiteral,
                Token.of(';')
        );
    }

    private TokenTree formatDocComment(final String docComment) {
        final TokenTree start = Token.of("/// <summary>");
        final TokenTree body = TokenTree.of(
                Arrays.stream(docComment.split("\n"))
                        .map(docLine -> TokenTree.of("///", docLine))).lineSeparated();
        final TokenTree end = Token.of("/// </summary>");
        return TokenTree.of(start, body, end).lineSeparated();
    }
}
