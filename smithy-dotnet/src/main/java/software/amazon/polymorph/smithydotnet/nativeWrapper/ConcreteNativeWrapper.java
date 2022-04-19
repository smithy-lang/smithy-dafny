// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.nativeWrapper;

import java.util.Optional;

import software.amazon.polymorph.smithydotnet.DotNetNameResolver;
import software.amazon.polymorph.smithydotnet.NativeWrapperCodegen;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.EntityShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ShapeId;

import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.classForCommonServiceException;
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
        final Optional<String> input = operationShape.getInput()
                .map(shapeId -> "%s %s".formatted(
                        nameResolver.dafnyTypeForShape(shapeId), INPUT));
        final String signature = "public %s %s(%s)".formatted(
                abstractDafnyOutput, methodName, input.orElse(""));
        final Optional<String> inputConversion = operationShape.getInput()
                .map(shapeId -> "%s %s = %s(%s);".formatted(
                        nameResolver.baseTypeForShape(shapeId),
                        NATIVE_INPUT,
                        qualifiedTypeConverter(shapeId, FROM_DAFNY),
                        INPUT));
        final TokenTree tryBlock = generateTryNativeCall(
                operationShape,
                methodName,
                input,
                concreteDafnyOutput);
        final TokenTree body = TokenTree.of(
                        TokenTree.of(inputConversion.orElse("")),
                        tryBlock,
                        generateCatchServiceException(concreteDafnyOutput),
                        generateCatchGeneralException(concreteDafnyOutput))
                .lineSeparated().braced();
        return TokenTree.of(TokenTree.of(signature), body).lineSeparated();
    }

    TokenTree generateTryNativeCall(
            OperationShape operationShape,
            String methodName,
            Optional<String> input,
            String concreteDafnyOutput
    ) {
        final Optional<String> nativeCallPrefix = operationShape.getOutput()
                .map(shapeId -> "%s %s = ".formatted(
                        nameResolver.baseTypeForShape(shapeId),
                        NATIVE_OUTPUT));
        final String nativeCall = "%s %s.%s(%s);".formatted(
                nativeCallPrefix.orElse(""),
                NATIVE_BASE_PROPERTY,
                methodName,
                input.isPresent() ? NATIVE_INPUT : "");
        final Optional<String> returnSuccessConversion = operationShape
                .getOutput()
                .map(shapeId -> "%s(%s)".formatted(
                        qualifiedTypeConverter(shapeId, TO_DAFNY),
                        NATIVE_OUTPUT));
        final String returnSuccess = "return %s.create_Success(%s);".formatted(
                concreteDafnyOutput, returnSuccessConversion.orElse(""));
        return TokenTree.of("try").append(
                TokenTree.of(nativeCall, returnSuccess).lineSeparated().braced()
        );
    }


     TokenTree generateCatchServiceException(final String dafnyOutput) {
        return generateCatch(
                dafnyOutput,
                classForCommonServiceException(serviceShape),
                Optional.empty()
        );
    }

    TokenTree generateCatchGeneralException(final String dafnyOutput) {
        return generateCatch(
                dafnyOutput,
                "Exception",
                Optional.of("new %s(e.Message)".formatted(
                        classForCommonServiceException(serviceShape)
                ))
        );
    }

    TokenTree generateCatch(
            final String dafnyOutput,
            final String caughtException,
            final Optional<String> castStatement
    ) {
        final String catchStatement = "catch(%s e)".formatted(caughtException);
        final String returnError = "return %s.create_Failure(%s(%s));".formatted(
                dafnyOutput,
                qualifiedTypeConverterForCommonError(serviceShape, TO_DAFNY),
                castStatement.orElse("e")
        );
        return TokenTree
                .of(catchStatement)
                .append(TokenTree.of(returnError).braced())
                .lineSeparated();
    }
}
