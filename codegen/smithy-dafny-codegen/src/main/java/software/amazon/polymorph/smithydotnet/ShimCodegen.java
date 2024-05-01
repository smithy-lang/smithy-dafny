// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.*;

import com.google.common.annotations.VisibleForTesting;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;

public class ShimCodegen {

  private final Model model;
  private final ServiceShape serviceShape;
  private final DotNetNameResolver nameResolver;

  static final String SHIM_UMWRAP_METHOD_NAME = "impl";
  private static final String IMPL_NAME = "_impl";
  private static final String INPUT_NAME = "input";
  private static final String INTERNAL_INPUT_NAME = "internalInput";
  private static final String RESULT_NAME = "result";

  public ShimCodegen(final Model model, final ServiceShape serviceShape) {
    this.model = model;
    this.serviceShape = serviceShape;
    this.nameResolver = new DotNetNameResolver(model, serviceShape);
  }

  // TODO: get smarter about imports. maybe just fully qualify all model-agnostic types?
  private static final List<String> UNCONDITIONAL_IMPORTS = List.of(
    "System",
    "System.IO",
    "System.Collections.Generic"
  );

  /**
   * Returns a map of service's and all resources' shim file paths to their generated ASTs.
   */
  public Map<Path, TokenTree> generate() {
    final Map<Path, TokenTree> codeByPath = new HashMap<>();

    // Use LinkedHashSet to dedupe while maintaining insertion order
    final LinkedHashSet<String> importNamespaces = new LinkedHashSet<>(
      UNCONDITIONAL_IMPORTS
    );
    importNamespaces.add(nameResolver.namespaceForService());
    importNamespaces.add(
      DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId(
        serviceShape.getId()
      )
    );
    final TokenTree prelude = TokenTree
      .of(importNamespaces.stream().map("using %s;"::formatted).map(Token::of))
      .lineSeparated();

    // Service shim
    final Path serviceShimPath = Path.of(
      String.format("%s.cs", nameResolver.clientForService())
    );
    final TokenTree serviceShimCode = generateServiceShim();
    codeByPath.put(serviceShimPath, serviceShimCode.prepend(prelude));

    // Resource shims
    model
      .getResourceShapes()
      .stream()
      .map(ResourceShape::getId)
      .filter(resourceShapeId ->
        ModelUtils.isInServiceNamespace(resourceShapeId, serviceShape)
      )
      .forEach(resourceShapeId -> {
        final Path resourceShimPath = Path.of(
          String.format(
            "%s.cs",
            nameResolver.shimClassForResource(resourceShapeId)
          )
        );
        final TokenTree resourceShim = generateResourceShim(resourceShapeId);
        codeByPath.put(resourceShimPath, resourceShim.prepend(prelude));
      });

    return codeByPath;
  }

  public TokenTree generateServiceShim() {
    final TokenTree header = Token.of(
      "public class %s".formatted(nameResolver.clientForService())
    );

    final TokenTree body = TokenTree
      .of(
        generateServiceImplDeclaration(serviceShape),
        generateServiceShimConstructor(),
        generateServiceShimDeconstructor(),
        generateServiceConstructor(serviceShape),
        generateServiceOperationShims(serviceShape.getId())
      )
      .lineSeparated();
    return header
      .append(body.braced())
      .namespaced(Token.of(nameResolver.namespaceForService()));
  }

  public TokenTree generateServiceShimConstructor() {
    return Token.of(
      """
      public %s(%s impl) {
          this.%s = impl;
      }""".formatted(
          nameResolver.clientForService(),
          nameResolver.dafnyTypeForShape(serviceShape.getId()),
          IMPL_NAME
        )
    );
  }

  public TokenTree generateServiceShimDeconstructor() {
    return Token.of(
      """
      public %s %s() {
          return this.%s;
      }""".formatted(
          nameResolver.dafnyTypeForShape(serviceShape.getId()),
          SHIM_UMWRAP_METHOD_NAME,
          IMPL_NAME
        )
    );
  }

  public TokenTree generateServiceImplDeclaration(ServiceShape serviceShape) {
    return Token.of(
      "private readonly %s %s;".formatted(
          nameResolver.dafnyTypeForShape(serviceShape.getId()),
          IMPL_NAME
        )
    );
  }

  public TokenTree generateServiceOperationShims(final ShapeId entityShapeId) {
    final EntityShape entityShape = model.expectShape(
      entityShapeId,
      EntityShape.class
    );
    return TokenTree
      .of(
        entityShape
          .getAllOperations()
          .stream()
          .map(this::generateServiceOperationShim)
      )
      .lineSeparated();
  }

  public TokenTree generateServiceOperationShim(
    final ShapeId operationShapeId
  ) {
    final OperationShape operationShape = model.expectShape(
      operationShapeId,
      OperationShape.class
    );

    final String outputType = operationShape
      .getOutput()
      .map(nameResolver::baseTypeForShape)
      .orElse("void");
    final String methodName = nameResolver.methodForOperation(operationShapeId);
    final String param = operationShape
      .getInput()
      .map(inputShapeId ->
        nameResolver.baseTypeForShape(inputShapeId) + " " + INPUT_NAME
      )
      .orElse("");
    final TokenTree signature = Token.of(
      "public %s %s(%s)".formatted(outputType, methodName, param)
    );

    final TokenTree convertInput = generateConvertInput(operationShapeId);
    final TokenTree callImpl = Token.of(
      "%s %s = %s.%s(%s);".formatted(
          nameResolver.dafnyTypeForServiceOperationOutput(operationShape),
          RESULT_NAME,
          IMPL_NAME,
          nameResolver.methodForOperation(operationShapeId),
          operationShape.getInput().isPresent() ? INTERNAL_INPUT_NAME : ""
        )
    );
    final TokenTree checkAndConvertFailure = generateCheckAndConvertFailure();
    final TokenTree convertAndReturnOutput = generateConvertAndReturnOutput(
      operationShapeId
    );

    return TokenTree
      .of(
        convertInput,
        callImpl,
        checkAndConvertFailure,
        convertAndReturnOutput
      )
      .lineSeparated()
      .braced()
      .prepend(signature);
  }

  public TokenTree generateServiceConstructor(final ServiceShape serviceShape) {
    final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(
      LocalServiceTrait.class
    );
    final StructureShape configShape = model.expectShape(
      localServiceTrait.getConfigId(),
      StructureShape.class
    );
    final TokenTree signature = TokenTree.of(
      "public %s(%s %s)".formatted(
          nameResolver.clientForService(),
          nameResolver.baseTypeForStructure(configShape),
          INPUT_NAME
        )
    );

    final TokenTree body = TokenTree
      .of(
        generateConvertShape(localServiceTrait.getConfigId()),
        Token.of(
          "%s %s = %s(%s);".formatted(
              // TODO really type me plz
              "var",
              RESULT_NAME,
              nameResolver.dafnyImplForServiceClient(),
              INTERNAL_INPUT_NAME
            )
        ),
        generateCheckAndConvertFailure(),
        Token.of("this._impl = %s.dtor_value;".formatted(RESULT_NAME))
      )
      .lineSeparated()
      .braced();

    return TokenTree.of(signature, body).lineSeparated();
  }

  public TokenTree generateConvertInput(final ShapeId operationShapeId) {
    final OperationShape operationShape = model.expectShape(
      operationShapeId,
      OperationShape.class
    );
    return TokenTree.of(
      operationShape
        .getInput()
        .map(this::generateConvertShape)
        .orElse(TokenTree.empty())
    );
  }

  public TokenTree generateConvertShape(final ShapeId shapeId) {
    return Token.of(
      "%s %s = %s(%s);".formatted(
          nameResolver.dafnyTypeForShape(shapeId),
          INTERNAL_INPUT_NAME,
          DotNetNameResolver.qualifiedTypeConverter(shapeId, TO_DAFNY),
          INPUT_NAME
        )
    );
  }

  public TokenTree generateCheckAndConvertFailure() {
    return Token.of(
      "if (%s.is_Failure) throw TypeConversion.FromDafny_CommonError(%s.dtor_error);".formatted(
          RESULT_NAME,
          RESULT_NAME
        )
    );
  }

  public TokenTree generateConvertAndReturnOutput(
    final ShapeId operationShapeId
  ) {
    final OperationShape operationShape = model.expectShape(
      operationShapeId,
      OperationShape.class
    );
    return Token.of(
      operationShape
        .getOutput()
        .map(outputShapeId ->
          "return %s(%s.dtor_value);".formatted(
              DotNetNameResolver.qualifiedTypeConverter(
                outputShapeId,
                FROM_DAFNY
              ),
              RESULT_NAME
            )
        )
        .orElse("")
    );
  }

  /**
   * Generate a shim that wraps a Dafny-compiled implementation of the given resource interface.
   *
   * TODO: generate a shim that wraps a native C# implementation (i.e. customer-implemented)
   */
  public TokenTree generateResourceShim(final ShapeId resourceShapeId) {
    final TokenTree header = Token.of(
      "internal class %s : %s".formatted(
          nameResolver.shimClassForResource(resourceShapeId),
          nameResolver.baseClassForResource(resourceShapeId)
        )
    );
    final TokenTree body = TokenTree
      .of(
        generateResourceImplDeclaration(resourceShapeId),
        generateResourceConstructor(resourceShapeId),
        generateOperationShims(resourceShapeId)
      )
      .lineSeparated();
    return header
      .append(body.braced())
      .namespaced(Token.of(nameResolver.namespaceForService()));
  }

  public TokenTree generateResourceConstructor(final ShapeId resourceShapeId) {
    return Token.of(
      "internal %s(%s impl) { this.%s = impl; }".formatted(
          nameResolver.shimClassForResource(resourceShapeId),
          nameResolver.dafnyTypeForShape(resourceShapeId),
          IMPL_NAME
        )
    );
  }

  public TokenTree generateResourceImplDeclaration(
    final ShapeId entityShapeId
  ) {
    return Token.of(
      "internal readonly %s %s;".formatted(
          nameResolver.dafnyTypeForShape(entityShapeId),
          IMPL_NAME
        )
    );
  }

  public TokenTree generateOperationShims(final ShapeId entityShapeId) {
    final EntityShape entityShape = model.expectShape(
      entityShapeId,
      EntityShape.class
    );
    return TokenTree
      .of(
        entityShape.getAllOperations().stream().map(this::generateOperationShim)
      )
      .lineSeparated();
  }

  public TokenTree generateOperationShim(final ShapeId operationShapeId) {
    final OperationShape operationShape = model.expectShape(
      operationShapeId,
      OperationShape.class
    );

    final String outputType = operationShape
      .getOutput()
      .map(nameResolver::baseTypeForShape)
      .orElse("void");
    final String methodName = nameResolver.abstractMethodForOperation(
      operationShapeId
    );
    final String param = operationShape
      .getInput()
      .map(inputShapeId ->
        nameResolver.baseTypeForShape(inputShapeId) + " " + INPUT_NAME
      )
      .orElse("");
    final TokenTree signature = Token.of(
      "protected override %s %s(%s)".formatted(outputType, methodName, param)
    );

    final TokenTree convertInput = generateConvertInput(operationShapeId);
    final TokenTree callImpl = Token.of(
      "%s %s = this.%s.%s(%s);".formatted(
          nameResolver.dafnyTypeForServiceOperationOutput(operationShape),
          RESULT_NAME,
          IMPL_NAME,
          nameResolver.methodForOperation(operationShapeId),
          operationShape.getInput().isPresent() ? INTERNAL_INPUT_NAME : ""
        )
    );
    final TokenTree checkAndConvertFailure = generateCheckAndConvertFailure();
    final TokenTree convertAndReturnOutput = generateConvertAndReturnOutput(
      operationShapeId
    );

    return TokenTree
      .of(
        convertInput,
        callImpl,
        checkAndConvertFailure,
        convertAndReturnOutput
      )
      .lineSeparated()
      .braced()
      .prepend(signature);
  }

  @VisibleForTesting
  public Model getModel() {
    return model;
  }

  @VisibleForTesting
  public DotNetNameResolver getNameResolver() {
    return nameResolver;
  }
}
