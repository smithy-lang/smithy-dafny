package software.amazon.polymorph.smithyrust.generator;

import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

public class MergedServicesGenerator {

  private final Model model;
  private final ServiceShape mainService;
  private final Set<String> namespaces;

  protected final Map<String, AbstractRustShimGenerator> generatorsByNamespace = new HashMap<>();

  public MergedServicesGenerator(Model model, ServiceShape mainService, Set<String> namespaces) {
    this.model = model;
    this.namespaces = namespaces;
    this.mainService = mainService;
  }

  public void generateAllNamespaces(final Path outputDir) {
    namespaces.stream()
      .map(namespace -> generatorForNamespace(model, namespace, namespaces))
      .forEach(generator -> generator.generate(outputDir));
  }

  protected AbstractRustShimGenerator generatorForNamespace(final Model model, final String namespace, final Set<String> namespaces) {
    return generatorsByNamespace.computeIfAbsent(namespace, n ->
      generatorFor(model, ModelUtils.serviceFromNamespace(model, n), namespaces));
  }

  public static AbstractRustShimGenerator generatorFor(Model model, ServiceShape serviceShape, Set<String> namespaces) {
    if (serviceShape.hasTrait(ServiceTrait.class)) {
      return new RustAwsSdkShimGenerator(model,
        serviceShape
      );
    } else {
      return new RustLibraryShimGenerator(
        model,
        serviceShape
      );
    }
  }

  private Stream<String> streamNamespacesToGenerateFor(Model model) {
    return model
      .shapes()
      .map(s -> s.getId().getNamespace())
      .distinct()
      .filter(this::shouldGenerateForNamespace);
  }

  private boolean shouldGenerateForNamespace(final String namespace) {
    return namespaces.contains(namespace);
  }

  private Stream<ServiceShape> streamServicesToGenerateFor(Model model) {
    return model.getServiceShapes().stream();
  }

  private RustFile depsModule(final ServiceShape serviceShape) {
    final TokenTree content;
    if (serviceShape.equals(mainService)) {
      content =
        declarePubModules(
          streamNamespacesToGenerateFor(model)
            .filter(n -> !n.equals(mainService.getId().getNamespace()))
            .map(NamespaceHelper::rustModuleForSmithyNamespace)
        );
    } else {
      content = declarePubModules(Stream.empty());
    }
    return new RustFile(
      rootPathForShape(serviceShape).resolve("deps.rs"),
      content
    );
  }

  private RustFile depModule(final String namespace) {
    final String rustModule = NamespaceHelper.rustModuleForSmithyNamespace(
      namespace
    );
    return new RustFile(
      Path.of("src", "deps", rustModule + ".rs"),
      TokenTree.of(RustLibraryShimGenerator.TOP_LEVEL_MOD_DECLS)
    );
  }
}
