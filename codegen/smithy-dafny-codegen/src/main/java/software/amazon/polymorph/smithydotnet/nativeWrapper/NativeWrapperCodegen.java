// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.nativeWrapper;

import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.*;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

import java.util.List;
import java.util.Optional;
import software.amazon.polymorph.smithydotnet.DotNetNameResolver;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.EntityShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

/**
 * NativeWrapperCodegen generates a Native Wrapper for a resource implemented in the native language.
 * <p>
 * To be concrete, at this time, it should be called for:
 * <ul>
 *   <li>ClientSupplier</li>
 *   <li>Keyring</li>
 *   <li>CryptographicMaterialsManager</li>
 * </ul>
 */
public class NativeWrapperCodegen {

  public final Model model;
  public final ServiceShape serviceShape;
  public final ResourceShape resourceShape;
  public final DotNetNameResolver nameResolver;
  public final ShapeId resourceShapeId;

  public static final String CLASS_PREFIX = "NativeWrapper";
  protected static final String NATIVE_BASE_PROPERTY = "_impl";
  protected static final String NATIVE_IMPL_INPUT = "nativeImpl";
  protected static final String NATIVE_INPUT = "nativeInput";
  protected static final String NATIVE_OUTPUT = "nativeOutput";
  protected static final String INPUT = "input";
  protected static final String IGNORE_IMPORT =
    """
    // ReSharper disable RedundantUsingDirective
    // ReSharper disable RedundantNameQualifier
    // ReSharper disable SuggestVarOrType_SimpleTypes
    """;
  protected static final List<String> UNCONDITIONAL_IMPORTS = List.of(
    "System",
    "_System",
    "Wrappers_Compile"
  );

  public NativeWrapperCodegen(
    final Model model,
    final ShapeId serviceShapeId,
    final ShapeId resourceShapeId,
    final DotNetNameResolver nameResolver
  ) {
    this.model = model;
    this.serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);
    this.resourceShape =
      model.expectShape(resourceShapeId, ResourceShape.class);
    this.nameResolver = nameResolver;
    this.resourceShapeId = resourceShapeId;
  }

  /**
   * Generates concrete NativeWrapper class, complete with import statements.
   */
  public TokenTree generate() {
    TokenTree clazz = generateClass();
    return TokenTree
      .of(getPrelude())
      .append(TokenTree.of("\n"))
      .append(clazz)
      .lineSeparated();
  }

  /**
   * Returns Import statement
   */
  static TokenTree getPrelude() {
    final TokenTree imports = TokenTree
      .of(
        UNCONDITIONAL_IMPORTS
          .stream()
          .map("using %s;"::formatted)
          .map(Token::of)
      )
      .lineSeparated();
    return TokenTree.of(IGNORE_IMPORT).append(imports);
  }

  TokenTree generateClass() {
    String className = nameResolver.nativeWrapperClassForResource(
      resourceShapeId
    );
    final TokenTree header = Token.of(
      "internal class %s : %s ".formatted(
          className,
          nameResolver.dafnyTypeForShape(resourceShapeId)
        )
    );
    final TokenTree nativeBaseProperty = TokenTree.of(
      "internal readonly %s %s;".formatted(
          nameResolver.baseClassForResource(resourceShapeId),
          NATIVE_BASE_PROPERTY
        )
    );
    final TokenTree constructor = generateConstructor(className);
    final TokenTree operationWrappers = TokenTree
      .of(
        model
          .expectShape(resourceShapeId, EntityShape.class)
          .getAllOperations()
          .stream()
          .map(this::generateOperationWrapper)
      )
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
    final String methodName =
      "public %s(%s %s)".formatted(
          className,
          nameResolver.baseClassForResource(resourceShapeId),
          NATIVE_IMPL_INPUT
        );
    final String body =
      "%s = %s;".formatted(NATIVE_BASE_PROPERTY, NATIVE_IMPL_INPUT);
    return TokenTree
      .of(methodName)
      .append(TokenTree.of(body).braced())
      .lineSeparated();
  }

  TokenTree generateOperationWrapper(final ShapeId operationShapeId) {
    final OperationShape operationShape = model.expectShape(
      operationShapeId,
      OperationShape.class
    );
    final String abstractDafnyOutput =
      nameResolver.dafnyTypeForServiceOperationOutput(operationShape);
    final String concreteDafnyOutput =
      nameResolver.dafnyTypeForServiceOperationOutput(operationShape, true);
    final String methodName = nameResolver.methodForOperation(operationShapeId);
    final Optional<String> nativeOutputType = operationShape
      .getOutput()
      .map(nameResolver::baseTypeForShape);

    final Optional<String> input = operationShape
      .getInput()
      .map(shapeId ->
        "%s %s".formatted(nameResolver.dafnyTypeForShape(shapeId), INPUT)
      );
    final String signature =
      "public %s %s(%s)".formatted(
          abstractDafnyOutput,
          methodName,
          input.orElse("")
        );
    final TokenTree inputConversion = generateInputConversion(
      operationShape.getInput()
    );
    final TokenTree tryBlock = generateTryNativeCall(
      operationShape,
      methodName,
      input,
      nativeOutputType,
      concreteDafnyOutput
    );
    final TokenTree body = TokenTree
      .of(
        generateValidateNativeOutputMethod(
          operationShape.getOutput(),
          nativeOutputType,
          methodName
        ),
        inputConversion,
        tryBlock,
        // See generateTryNativeCall for details on why we MUST try/catch here.
        generateCatchThatReturnsFailure("Exception", concreteDafnyOutput)
      )
      .lineSeparated()
      .braced();

    // The current Dafny generates a public method and `method'`.
    // This means that Dafny can hook this function
    // and provide a clean interface for validated mocks.
    // However, this exposes this name publicly.
    // TODO migrate the internal construction to abstract modules
    final String signature_K =
      "public %s %s_k(%s)".formatted(
          abstractDafnyOutput,
          methodName,
          input.orElse("")
        );
    final TokenTree body_k = TokenTree
      .of(
        "throw new %s(\"Not supported at this time.\");".formatted(
            classForConcreteServiceException(serviceShape)
          )
      )
      .braced();

    return TokenTree
      .of(TokenTree.of(signature), body, TokenTree.of(signature_K), body_k)
      .lineSeparated();
  }

  TokenTree generateInputConversion(Optional<ShapeId> inputShapeId) {
    if (inputShapeId.isEmpty()) return TokenTree.empty();
    return TokenTree.of(
      "%s %s = %s(%s);".formatted(
          nameResolver.baseTypeForShape(inputShapeId.get()),
          NATIVE_INPUT,
          qualifiedTypeConverter(inputShapeId.get(), FROM_DAFNY),
          INPUT
        )
    );
  }

  // This is calling the underlying native implementation
  // of a Dafny interface.
  // This means we are leaving the verified boundary
  // and crossing into the native runtime.
  // This is problematic because Dafny expects
  // to be able to reason about this component.
  // Dafny expects that this will return a Result.
  // But more importantly, that it MUST NOT throw.
  // This is because Dafny does not have throw/try/catch semantics.
  // If a natively implemented resource throws unexpectedly,
  // this can introduce unsoundness into our Dafny model.
  // Therefore, we MUST try and then wrap the error
  // so that we can return a Dafny result.
  TokenTree generateTryNativeCall(
    OperationShape operationShape,
    String methodName,
    Optional<String> input,
    Optional<String> nativeOutputType,
    String concreteDafnyOutput
  ) {
    final Optional<String> nativeCallPrefix = nativeOutputType.map(s ->
      "%s %s =".formatted(s, NATIVE_OUTPUT)
    );
    final TokenTree nativeCall = TokenTree.of(
      "%s %s.%s(%s);".formatted(
          nativeCallPrefix.orElse(""),
          NATIVE_BASE_PROPERTY,
          methodName,
          input.isPresent() ? NATIVE_INPUT : ""
        )
    );
    final TokenTree isNativeOutputNull = generateIsNativeOutputNull(
      methodName,
      nativeOutputType
    );
    final TokenTree validateNativeOutput = generateValidateNativeOutput(
      operationShape.getOutput()
    );
    final Optional<String> successConversion = operationShape
      .getOutput()
      .map(shapeId ->
        "%s(%s)".formatted(
            qualifiedTypeConverter(shapeId, TO_DAFNY),
            NATIVE_OUTPUT
          )
      );
    final String outputType = operationShape
      .getOutput()
      .map(nameResolver::dafnyTypeForShape)
      .orElse(nameResolver.dafnyTypeForUnit())
      .replace("_System._I", "");
    final TokenTree returnSuccess = TokenTree.of(
      "return %s.create_Success(%s);".formatted(
          concreteDafnyOutput,
          successConversion.orElse("%s.create()".formatted(outputType))
        )
    );

    return TokenTree
      .of("try")
      .append(
        TokenTree
          .of(
            nativeCall,
            isNativeOutputNull,
            validateNativeOutput,
            returnSuccess
          )
          .lineSeparated()
          .braced()
      );
  }

  TokenTree generateIsNativeOutputNull(
    String methodName,
    Optional<String> nativeOutputType
  ) {
    if (nativeOutputType.isEmpty()) return TokenTree.empty();
    final String nullMessage =
      "$\"{%s}._%s returned null, should be {typeof(%s)}\"".formatted(
          NATIVE_BASE_PROPERTY,
          methodName,
          nativeOutputType.get()
        );
    final String exception = classForConcreteServiceException(serviceShape);
    final String nullCheck =
      "_ = %s ?? throw new %s(%s);".formatted(
          NATIVE_OUTPUT,
          exception,
          nullMessage
        );
    return TokenTree.of(nullCheck);
  }

  TokenTree generateValidateNativeOutput(Optional<ShapeId> outputShapeId) {
    if (outputShapeId.isEmpty()) return TokenTree.empty();
    StructureShape structureShape = model.expectShape(
      outputShapeId.get(),
      StructureShape.class
    );
    if (
      structureShape.hasTrait(PositionalTrait.class)
    ) return TokenTree.empty();
    return TokenTree.of("validateOutput(%s);".formatted(NATIVE_OUTPUT));
  }

  TokenTree generateValidateNativeOutputMethod(
    Optional<ShapeId> outputShapeId,
    Optional<String> nativeOutputType,
    String methodName
  ) {
    if (
      outputShapeId.isEmpty() || nativeOutputType.isEmpty()
    ) return TokenTree.empty();
    StructureShape structureShape = model.expectShape(
      outputShapeId.get(),
      StructureShape.class
    );
    if (
      structureShape.hasTrait(PositionalTrait.class)
    ) return TokenTree.empty();
    final String signature =
      "void validateOutput(%s %s)".formatted(
          nativeOutputType.get(),
          NATIVE_OUTPUT
        );
    final String tryCatch =
      "try { %s.Validate(); } catch (ArgumentException e)".formatted(
          NATIVE_OUTPUT
        );
    final TokenTree catchBlock = TokenTree
      .of(
        "var message = $\"Output of {%s}._%s is invalid. {e.Message}\";".formatted(
            NATIVE_BASE_PROPERTY,
            methodName
          ),
        "throw new %s(message);".formatted(
            classForConcreteServiceException(serviceShape)
          )
      )
      .lineSeparated()
      .braced();
    final TokenTree body = TokenTree
      .of(TokenTree.of(tryCatch), catchBlock)
      .lineSeparated()
      .braced();
    return TokenTree.of(signature).append(body);
  }

  TokenTree generateCatchThatReturnsFailure(
    final String caughtException,
    final String dafnyOutput
  ) {
    final String catchStatement = "catch(%s e)".formatted(caughtException);
    final TokenTree caughtStatement = TokenTree.of(
      "return %s.create_Failure(%s(e));".formatted(
          dafnyOutput,
          nameResolver.qualifiedTypeConverterForCommonError(
            serviceShape,
            TO_DAFNY
          )
        )
    );
    return TokenTree
      .of(catchStatement)
      .append(TokenTree.of(caughtStatement).braced())
      .lineSeparated();
  }
}
