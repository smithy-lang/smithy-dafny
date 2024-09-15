package software.amazon.polymorph.smithyrust.generator;

import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
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

  public boolean isMainService(ServiceShape serviceShape) {
    return serviceShape.equals(mainService);
  }

  public boolean isMainNamespace(String namespace) {
    return isMainService(ModelUtils.serviceFromNamespace(model, namespace));
  }

  public Set<RustFile> rustFiles() {
    Set<RustFile> rustFiles = new HashSet<>();

    namespaces.stream()
      .map(namespace -> generatorForNamespace(model, namespace, namespaces))
      .flatMap(generator -> generator.rustFiles().stream())
      .forEach(rustFiles::add);

    streamNamespacesToGenerateFor(model)
      .filter(n -> !isMainNamespace(n))
      .map(n -> depTopLevelModule(n))
      .forEach(rustFiles::add);

    rustFiles.add(topLevelDepsModule());

    return rustFiles;
  }

  public void generateAllNamespaces(final Path outputDir) {
    Set<RustFile> rustFiles = rustFiles();

    final LinkedHashMap<Path, TokenTree> tokenTreeMap = new LinkedHashMap<>();
    for (RustFile rustFile : rustFiles) {
      tokenTreeMap.put(rustFile.path(), rustFile.content());
    }
    IOUtils.writeTokenTreesIntoDir(tokenTreeMap, outputDir);
  }

  protected AbstractRustShimGenerator generatorForNamespace(final Model model, final String namespace, final Set<String> namespaces) {
    return generatorsByNamespace.computeIfAbsent(namespace, n ->
      generatorFor(model, ModelUtils.serviceFromNamespace(model, n), namespaces));
  }

  public AbstractRustShimGenerator generatorFor(Model model, ServiceShape serviceShape, Set<String> namespaces) {
    if (serviceShape.hasTrait(ServiceTrait.class)) {
      return new RustAwsSdkShimGenerator(
        this,
        model,
        serviceShape
      );
    } else {
      return new RustLibraryShimGenerator(
        this,
        model,
        serviceShape
      );
    }
  }

  public Stream<String> streamNamespacesToGenerateFor(Model model) {
    return model
      .shapes()
      .map(s -> s.getId().getNamespace())
      .distinct()
      .filter(this::shouldGenerateForNamespace);
  }

  private boolean shouldGenerateForNamespace(final String namespace) {
    return namespaces.contains(namespace);
  }

  public Stream<ServiceShape> streamServicesToGenerateFor(Model model) {
    return model.getServiceShapes().stream();
  }

  private RustFile depTopLevelModule(final String namespace) {
    final String rustModule = RustUtils.rustModuleForSmithyNamespace(
      namespace
    );
    return new RustFile(
      Path.of("src", "deps", rustModule + ".rs"),
      TokenTree.of(RustLibraryShimGenerator.TOP_LEVEL_MOD_DECLS)
    );
  }

  // TODO: overlap with library version
  private RustFile topLevelDepsModule() {
    final TokenTree content =
        RustUtils.declarePubModules(
          streamServicesToGenerateFor(model)
            .filter(s -> !isMainService(s))
            .map(s -> s.getId().getNamespace())
            .map(RustUtils::rustModuleForSmithyNamespace)
        );
    return new RustFile(
      Path.of("src", "deps.rs"),
      content
    );
  }
}
