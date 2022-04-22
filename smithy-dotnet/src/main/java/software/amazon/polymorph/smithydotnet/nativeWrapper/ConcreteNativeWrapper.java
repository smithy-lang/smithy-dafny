// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.nativeWrapper;

import java.util.Optional;

import software.amazon.polymorph.smithydotnet.DotNetNameResolver;
import software.amazon.polymorph.smithydotnet.NativeWrapperCodegen;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.EntityShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.classForConcreteServiceException;
import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.qualifiedTypeConverter;
import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.qualifiedTypeConverterForCommonError;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

public class ConcreteNativeWrapper extends NativeWrapperCodegen {

    public ConcreteNativeWrapper(Model model, ShapeId serviceShapeId, ShapeId resourceShapeId, DotNetNameResolver nameResolver) {
        super(model, serviceShapeId, resourceShapeId, nameResolver);
    }

    public TokenTree generate() {
        return generateConcrete();
    }

    /**
     * Generates concrete NativeWrapper class, complete with copyright
     * and import statements.
     */
    public TokenTree generateConcrete() {
        TokenTree clazz = generateClass();
        return TokenTree
                .of(getPrelude())
                .append(TokenTree.of("\n"))
                .append(clazz)
                .lineSeparated();
    }

    TokenTree generateClass() {
        String className = nameResolver.nativeWrapperClassForResource(resourceShapeId);
        final TokenTree header = Token.of("internal class %s : %s ".formatted(
                className,
                nameResolver.dafnyTypeForShape(resourceShapeId)
        ));
        final TokenTree nativeBaseProperty = TokenTree.of(
                "internal readonly %s %s;".formatted(
                        nameResolver.baseClassForResource(resourceShapeId),
                        NATIVE_BASE_PROPERTY
                ));
        final TokenTree constructor = generateConstructor(className);
        final TokenTree operationWrappers = TokenTree.of(
                model.expectShape(resourceShapeId, EntityShape.class)
                        .getAllOperations().stream()
                        .map(this::generateOperationWrapper))
                .lineSeparated();
        final TokenTree body = TokenTree
                .of(nativeBaseProperty, constructor, operationWrappers)
                .lineSeparated()
                .braced();
        return header
                .append(body)
                .lineSeparated()
                .namespaced(Token.of(nameResolver.namespaceForService()));
    }

    TokenTree generateConstructor(String className) {
        final String methodName = "public %s(%s %s)".formatted(
                className,
                nameResolver.baseClassForResource(resourceShapeId),
                NATIVE_IMPL_INPUT
        );
        final String body = "%s = %s;".formatted(
                NATIVE_BASE_PROPERTY,
                NATIVE_IMPL_INPUT
        );
        return TokenTree.of(methodName)
                .append(TokenTree.of(body).braced())
                .lineSeparated();
    }

     TokenTree generateOperationWrapper(final ShapeId operationShapeId) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final String abstractDafnyOutput = nameResolver.dafnyTypeForServiceOperationOutput(operationShape);
        final String concreteDafnyOutput = nameResolver.dafnyTypeForServiceOperationOutput(operationShape, true);
        final String methodName = nameResolver.methodForOperation(operationShapeId);
        final Optional<String> nativeOutputType = operationShape.getOutput()
                .map(nameResolver::baseTypeForShape);

        final Optional<String> input = operationShape.getInput()
                .map(shapeId -> "%s %s".formatted(
                        nameResolver.dafnyTypeForShape(shapeId), INPUT));
        final String signature = "public %s %s(%s)".formatted(
                abstractDafnyOutput, methodName, input.orElse(""));
        final TokenTree inputConversion = generateInputConversion(operationShape.getInput());
        final TokenTree tryBlock = generateTryNativeCall(
                operationShape,
                methodName,
                input,
                nativeOutputType,
                concreteDafnyOutput);
        final TokenTree body = TokenTree.of(
                generateValidateNativeOutputMethod(
                        operationShape.getOutput(), nativeOutputType,methodName),
                inputConversion,
                TokenTree.of("%s finalException = null;"
                        .formatted(classForConcreteServiceException(serviceShape))),
                tryBlock,
                generateCatchServiceException(),
                generateCatchGeneralException(),
                generateReturnFailure(concreteDafnyOutput)
                )
                .lineSeparated().braced();
        return TokenTree.of(TokenTree.of(signature), body).lineSeparated();
    }

    TokenTree generateInputConversion(Optional<ShapeId> inputShapeId) {
        if (inputShapeId.isEmpty()) return TokenTree.empty();
        return TokenTree.of("%s %s = %s(%s);".formatted(
                nameResolver.baseTypeForShape(inputShapeId.get()),
                NATIVE_INPUT,
                qualifiedTypeConverter(inputShapeId.get(), FROM_DAFNY),
                INPUT));
    }

    TokenTree generateTryNativeCall(
            OperationShape operationShape,
            String methodName,
            Optional<String> input,
            Optional<String> nativeOutputType,
            String concreteDafnyOutput
    ) {
        final Optional<String> nativeCallPrefix =
                nativeOutputType.map(s -> "%s %s =".formatted(
                        s, NATIVE_OUTPUT));
        final TokenTree nativeCall = TokenTree.of("%s %s.%s(%s);".formatted(
                nativeCallPrefix.orElse(""), NATIVE_BASE_PROPERTY,
                methodName, input.isPresent() ? NATIVE_INPUT : ""));
        final TokenTree isNativeOutputNull = generateIsNativeOutputNull(
                methodName, nativeOutputType);
        final TokenTree validateNativeOutput = generateValidateNativeOutput(
                operationShape.getOutput());
        final Optional<String> successConversion = operationShape
                .getOutput()
                .map(shapeId -> "%s(%s)".formatted(
                        qualifiedTypeConverter(shapeId, TO_DAFNY),
                        NATIVE_OUTPUT));
        final TokenTree returnSuccess = TokenTree.of("return %s.create_Success(%s);".formatted(
                concreteDafnyOutput, successConversion.orElse("")));
        return TokenTree.of("try").append(
                TokenTree.of(nativeCall, isNativeOutputNull, validateNativeOutput, returnSuccess)
                    .lineSeparated().braced()
        );
    }

    TokenTree generateIsNativeOutputNull(
            String methodName,
            Optional<String> nativeOutputType
    ) {
        if (nativeOutputType.isEmpty()) return TokenTree.empty();
        final String message_one = "$\"Output of {%s}._%s is invalid. \""
                .formatted(NATIVE_BASE_PROPERTY, methodName);
        final String message_two = "$\"Should be {typeof(%s)} but is null.\""
                .formatted(nativeOutputType.get());
        final String exception = classForConcreteServiceException(serviceShape);
        final String nullCheck = "_ = %s ?? throw new %s(\n%s +\n%s);"
                .formatted(NATIVE_OUTPUT, exception, message_one, message_two);
        return TokenTree.of(nullCheck);
    }

    TokenTree generateValidateNativeOutput(Optional<ShapeId> outputShapeId) {
        if (outputShapeId.isEmpty()) return TokenTree.empty();
        StructureShape structureShape = model.expectShape(outputShapeId.get(), StructureShape.class);
        if (structureShape.hasTrait(PositionalTrait.class)) return TokenTree.empty();
        return TokenTree.of("validateOutput(%s);".formatted(NATIVE_OUTPUT));
    }

    TokenTree generateValidateNativeOutputMethod(
            Optional<ShapeId> outputShapeId,
            Optional<String> nativeOutputType,
            String methodName
    ) {
        if (outputShapeId.isEmpty() || nativeOutputType.isEmpty()) return TokenTree.empty();
        StructureShape structureShape = model.expectShape(outputShapeId.get(), StructureShape.class);
        if (structureShape.hasTrait(PositionalTrait.class)) return TokenTree.empty();
        final String signature = "void validateOutput(%s %s)".formatted(
                nativeOutputType.get(), NATIVE_OUTPUT
        );
        final String tryCatch = "try { %s.Validate(); } catch (ArgumentException e)"
                .formatted(NATIVE_OUTPUT);
        final TokenTree catchBlock = TokenTree.of(
                "var message = $\"Output of {%s}._%s is invalid. {e.Message}\";"
                    .formatted(NATIVE_BASE_PROPERTY, methodName),
                "throw new %s(message);"
                    .formatted(classForConcreteServiceException(serviceShape))
                )
                .lineSeparated().braced();
        final TokenTree body = TokenTree.of(TokenTree.of(tryCatch), catchBlock)
                .lineSeparated().braced();
        return TokenTree.of(signature).append(body);
    }


     TokenTree generateCatchServiceException() {
        return generateCatch(
                classForConcreteServiceException(serviceShape),
                Optional.empty()
        );
    }

    TokenTree generateCatchGeneralException() {
        return generateCatch(
                "Exception",
                Optional.of("new %s(e.Message)".formatted(
                        classForConcreteServiceException(serviceShape)
                ))
        );
    }

    TokenTree generateCatch(
            final String caughtException,
            final Optional<String> castStatement
    ) {
        final String catchStatement = "catch(%s e)".formatted(caughtException);
        final String setFinalException = "finalException = %s;".formatted(
                castStatement.orElse("e")
        );
        return TokenTree
                .of(catchStatement)
                .append(TokenTree.of(setFinalException).braced())
                .lineSeparated();
    }

    TokenTree generateReturnFailure(String dafnyOutput) {
        return TokenTree.of("return %s.create_Failure(%s(finalException));".
                formatted(
                        dafnyOutput,
                        qualifiedTypeConverterForCommonError(serviceShape, TO_DAFNY)
        ));
    }
}
