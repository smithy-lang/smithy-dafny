// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithydotnet.localServiceWrapper;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import software.amazon.polymorph.smithydotnet.ServiceCodegen;
import software.amazon.polymorph.smithydotnet.nativeWrapper.NativeWrapperCodegen;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;

public class LocalServiceWrappedCodegen extends ServiceCodegen {

  public LocalServiceWrappedCodegen(
    final Model model,
    final ServiceShape serviceShape
  ) {
    super(
      model,
      serviceShape,
      new LocalServiceWrappedNameResolver(model, serviceShape)
    );
  }

  @Override
  public Map<Path, TokenTree> generate() {
    final Map<Path, TokenTree> codeByPath = new HashMap<>();

    // TODO see: generateWrappedServiceExtern The extern for wrapping can be fully generated

    // Resources
    model
      .getResourceShapes()
      .stream()
      .map(ResourceShape::getId)
      .filter(resourceShapeId ->
        ModelUtils.isInServiceNamespace(resourceShapeId, serviceShape)
      )
      .forEach(resourceShapeId -> {
        if (shouldGenerateNativeWrapper(resourceShapeId)) {
          // This SHOULD be a shared component without any changes.
          // If the wrapped version begins to differ from the native type
          // then this wrapped version begins to be a less valuable test bed.
          final NativeWrapperCodegen nativeWrapperCodegen =
            new NativeWrapperCodegen(
              model,
              serviceShape.getId(),
              resourceShapeId,
              nameResolver
            );
          final Path nativeWrapperPath = Path.of(
            String.format(
              "%s.cs",
              nameResolver.nativeWrapperClassForResource(resourceShapeId)
            )
          );
          final TokenTree nativeWrapperClass = nativeWrapperCodegen.generate();
          codeByPath.put(nativeWrapperPath, nativeWrapperClass);
        }
      });

    return codeByPath;
  }

  public TokenTree generateWrappedServiceExtern(
    final ServiceShape serviceShape
  ) {
    if (
      !serviceShape.hasTrait(LocalServiceTrait.class)
    ) throw new IllegalStateException("MUST be an LocalService");
    final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(
      LocalServiceTrait.class
    );

    final String configTypeName = localServiceTrait.getConfigId().getName();

    final TokenTree defaultClass = TokenTree.of(
      "public partial class __default"
    );

    final TokenTree externSignature = TokenTree
      .of(
        "public static",
        // TODO fix the Error and don't hard code it :(
        "Wrappers_Compile._IResult<Types.%s,Types._IError>".formatted(
            nameResolver.dafnyTypeForShape(serviceShape.getId())
          ),
        "Wrapped%s(Types.%s config)".formatted(
            localServiceTrait.getSdkId(),
            configTypeName
          )
      )
      .lineSeparated();

    final TokenTree externBody = TokenTree
      .of(
        "var wrappedConfig = %s(config);".formatted("asdf"),
        "var impl = new %s(wrappedConfig);".formatted(
            ((LocalServiceWrappedNameResolver) nameResolver).implForServiceClient()
          ),
        "var wrappedClient = new %s(impl);".formatted(
            ((LocalServiceWrappedNameResolver) nameResolver).shimClassForService()
          ),
        // TODO fix the Error and don't hard code it :(
        "return Wrappers_Compile.Result<Types.%s,Types._IError>.create_Success(wrappedClient);".formatted(
            nameResolver.dafnyTypeForShape(serviceShape.getId())
          )
      )
      .lineSeparated();

    return defaultClass
      .append(externSignature.append(externBody.braced()).braced())
      .namespaced(
        DafnyNameResolverHelpers.packageNameForNamespace(
          serviceShape.getId().getNamespace()
        ) +
        ".Wrapped"
      );
  }
}
