package software.amazon.polymorph.smithyrust.generator;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;
import software.amazon.polymorph.CodegenEngine;
import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;

public class MergedServicesGenerator {

  private final Model model;
  private final ServiceShape mainService;
  private final Set<String> namespaces;
  private final boolean generateWrappedClient;
  private final Set<CodegenEngine.GenerationAspect> generationAspects;

  protected final Map<String, AbstractRustShimGenerator> generatorsByNamespace =
    new HashMap<>();

  public MergedServicesGenerator(
    Model model,
    ServiceShape mainService,
    Set<String> namespaces,
    boolean generateWrappedClient,
    Set<CodegenEngine.GenerationAspect> generationAspects
  ) {
    this.model = model;
    this.namespaces = namespaces;
    this.mainService = mainService;
    this.generateWrappedClient = generateWrappedClient;
    this.generationAspects = generationAspects;

    // Prepopulate generators
    for (String namespace : namespaces) {
      generatorForNamespace(model, namespace, namespaces);
    }
  }

  public boolean isMainService(ServiceShape serviceShape) {
    return serviceShape.equals(mainService);
  }

  public boolean isMainNamespace(String namespace) {
    return isMainService(ModelUtils.serviceFromNamespace(model, namespace));
  }

  public Set<RustFile> rustFiles() {
    Set<RustFile> rustFiles = new HashSet<>();

    namespaces
      .stream()
      .map(namespace -> generatorForNamespace(model, namespace, namespaces))
      .flatMap(generator -> generator.rustFiles().stream())
      .forEach(rustFiles::add);

    streamNamespacesToGenerateFor(model)
      .filter(n -> !isMainNamespace(n))
      .map(namespace -> generatorForNamespace(model, namespace, namespaces))
      .map(g -> g.depTopLevelModule())
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

  protected AbstractRustShimGenerator generatorForNamespace(
    final Model model,
    final String namespace,
    final Set<String> namespaces
  ) {
    return generatorsByNamespace.computeIfAbsent(
      namespace,
      n ->
        generatorFor(
          model,
          ModelUtils.serviceFromNamespace(model, n),
          namespaces
        )
    );
  }

  public AbstractRustShimGenerator generatorFor(
    Model model,
    ServiceShape serviceShape,
    Set<String> namespaces
  ) {
    if (serviceShape.hasTrait(ServiceTrait.class)) {
      return new RustAwsSdkShimGenerator(
        this,
        model,
        serviceShape,
        generationAspects
      );
    } else {
      return new RustLibraryShimGenerator(
        this,
        model,
        serviceShape,
        generateWrappedClient
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

  // TODO: overlap with library version
  private RustFile topLevelDepsModule() {
    final TokenTree content = RustUtils.declarePubModules(
      streamServicesToGenerateFor(model)
        .filter(s -> !isMainService(s))
        .map(s -> s.getId().getNamespace())
        .map(RustUtils::rustModuleForSmithyNamespace)
    );
    return new RustFile(Path.of("src", "deps.rs"), content);
  }

  public AbstractRustShimGenerator generatorForShape(final Shape shape) {
    return generatorsByNamespace.get(shape.getId().getNamespace());
  }
}
