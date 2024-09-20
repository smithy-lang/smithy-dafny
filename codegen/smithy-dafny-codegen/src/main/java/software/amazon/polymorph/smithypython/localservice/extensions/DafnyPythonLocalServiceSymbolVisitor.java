package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import java.util.Locale;
import java.util.Optional;
import java.util.Set;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.DafnyLocalServiceCodegenConstants;
import software.amazon.polymorph.smithypython.localservice.customize.ReferencesFileWriter;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.*;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.MediaTypeTrait;
import software.amazon.smithy.python.codegen.CodegenUtils;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.SmithyPythonDependency;
import software.amazon.smithy.python.codegen.SymbolVisitor;
import software.amazon.smithy.utils.CaseUtils;
import software.amazon.smithy.utils.MediaType;
import software.amazon.smithy.utils.StringUtils;

/**
 * Override Smithy-Python's SymbolVisitor to support namespaces in other modules and
 * Smithy-Dafny-specific traits.
 */
public class DafnyPythonLocalServiceSymbolVisitor extends SymbolVisitor {

  public DafnyPythonLocalServiceSymbolVisitor(
    Model model,
    PythonSettings settings
  ) {
    super(model, settings);
  }

  /**
   * Override Smithy-Python to support namespaces in other modules.
   * @param namespace
   * @param filename
   * @return
   */
  protected String getSymbolNamespacePathForNamespaceAndFilename(
    String namespace,
    String filename
  ) {
    return format(
      "%s.%s",
      SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
        namespace,
        settings
      ),
      filename
    );
  }

  /**
   * Override Smithy-Python to support namespaces in other modules.
   * @param namespace
   * @param filename
   * @return
   */
  protected String getSymbolDefinitionFilePathForNamespaceAndFilename(
    String namespace,
    String filename
  ) {
    String directoryFilePath;
    if ("smithy.api".equals(namespace)) {
      directoryFilePath =
        SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
          settings.getService().getNamespace()
        );
    } else {
      directoryFilePath =
        SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
          namespace
        );
    }

    return format("./%s/%s.py", directoryFilePath, filename);
  }

  /**
   * Override Smithy-Python's serviceShape to only generate shapes for this namespace's localService
   *  and to properly typehint boto3 clients.
   * @param serviceShape
   * @return
   */
  @Override
  public Symbol serviceShape(ServiceShape serviceShape) {
    String generationPath =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        settings.getService().getNamespace()
      );

    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      String name = getDefaultShapeName(serviceShape);
      String filename = "client";
      String definitionFile = serviceShape.getId().equals(settings.getService())
        ? getSymbolDefinitionFilePathForNamespaceAndFilename(
          serviceShape.getId().getNamespace(),
          filename
        )
        // Smithy and Smithy-Python will always attempt to write a referenced symbol.
        // There is no way to disable writing referenced symbols, even for externally-defined
        // symbols.
        // We don't want to write a LocalService symbol, since it is either in this project's
        // `client.py`,
        //   or is already written in another project's `client.py`.
        // As a workaround, dump dependency localService symbols to a file that will be
        // deleted after codegen.
        // Typehints will reference the `namespace` and `serviceShape` name and not this file.
        : generationPath +
        "/" +
        DafnyLocalServiceCodegenConstants.LOCAL_SERVICE_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME +
        ".py";
      return createSymbolBuilder(
        serviceShape,
        name,
        getSymbolNamespacePathForNamespaceAndFilename(
          serviceShape.getId().getNamespace(),
          filename
        )
      )
        .definitionFile(definitionFile)
        .build();
    } else if (AwsSdkNameResolver.isAwsSdkShape(serviceShape)) {
      return createSymbolBuilder(serviceShape, "BaseClient", "botocore.client")
        // Same as above; there is no way to disable writing referenced symbols.
        // Dump boto3 client type into a file that will be deleted after codegen.
        // Typehints will reference boto3 clients as `botocore.client.BaseClient`.
        .definitionFile(
          generationPath +
          "/" +
          DafnyLocalServiceCodegenConstants.LOCAL_SERVICE_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME +
          ".py"
        )
        .build();
    } else {
      throw new IllegalArgumentException(
        "ServiceShape not supported: " + serviceShape
      );
    }
  }

  /**
   * Override Smithy-Python's resourceShape to handle writing resource shapes.
   * @param resourceShape
   * @return
   */
  @Override
  public Symbol resourceShape(ResourceShape resourceShape) {
    var name = getDefaultShapeName(resourceShape);
    String filename = "references";

    String generationPath =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        settings.getService().getNamespace()
      );

    // Smithy and Smithy-Python will always attempt to write a referenced symbol.
    // There is no way to disable writing referenced symbols, even for externally-defined symbols.
    // We don't want to write a resource reference symbol, since it is either in this project's
    // `references.py`,
    //   or is already written in another project's `references.py`.
    // As a workaround, dump dependency reference symbols to a file that will be deleted after
    // codegen.
    // Typehints will reference the `namespace` and `resourceShape` name and not this file.
    return createSymbolBuilder(
      resourceShape,
      name,
      getSymbolNamespacePathForNamespaceAndFilename(
        resourceShape.getId().getNamespace(),
        filename
      )
    )
      .definitionFile(
        generationPath +
        "/" +
        DafnyLocalServiceCodegenConstants.LOCAL_SERVICE_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME +
        ".py"
      )
      .putProperty("stdlib", true)
      .build();
  }

  /**
   * Override Smithy-Python to handle other namespaces and Polymorph custom traits.
   * @param shape
   * @return
   */
  @Override
  public Symbol structureShape(StructureShape shape) {
    String name = getDefaultShapeName(shape);
    if (shape.hasTrait(ErrorTrait.class)) {
      String filename = "errors";
      return createSymbolBuilder(
        shape,
        name,
        getSymbolNamespacePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
        .definitionFile(
          getSymbolDefinitionFilePathForNamespaceAndFilename(
            shape.getId().getNamespace(),
            filename
          )
        )
        .build();
    }

    Set<ShapeId> localServiceConfigShapes =
      SmithyNameResolver.getLocalServiceConfigShapes(model);
    if (localServiceConfigShapes.contains(shape.getId())) {
      String filename = "config";
      return createSymbolBuilder(
        shape,
        name,
        getSymbolNamespacePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
        .definitionFile(
          getSymbolDefinitionFilePathForNamespaceAndFilename(
            shape.getId().getNamespace(),
            filename
          )
        )
        .build();
    }

    if (shape.hasTrait(PositionalTrait.class)) {
      String filename = "models";
      String generationPath =
        SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
          settings.getService().getNamespace()
        );
      MemberShape memberShape = PositionalTrait.onlyMember(shape);
      ShapeId targetShapeId = memberShape.getTarget();
      Shape targetShape = model.expectShape(targetShapeId);
      String targetShapeName = getDefaultShapeName(targetShape);
      if (targetShape.hasTrait(ReferenceTrait.class)) {
        return structureShape(targetShape.asStructureShape().get());
      }
      return createSymbolBuilder(
        targetShape,
        targetShapeName,
        getSymbolNamespacePathForNamespaceAndFilename(
          targetShapeId.getNamespace(),
          filename
        )
      )
        .definitionFile(
          generationPath +
          "/" +
          DafnyLocalServiceCodegenConstants.LOCAL_SERVICE_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME +
          ".py"
        )
        .putProperty("stdlib", true)
        .build();
    }

    if (shape.hasTrait(ReferenceTrait.class)) {
      ShapeId referentShapeId = shape
        .expectTrait(ReferenceTrait.class)
        .getReferentId();
      Shape referentShape = model.expectShape(referentShapeId);
      if (referentShape.isResourceShape()) {
        return resourceShape(referentShape.asResourceShape().get());
      }
      if (referentShape.isServiceShape()) {
        return serviceShape(referentShape.asServiceShape().get());
      } else {
        throw new IllegalArgumentException(
          "Referent shape is not of a supported type: " + shape
        );
      }
    }

    String filename = "models";
    return createSymbolBuilder(
      shape,
      name,
      getSymbolNamespacePathForNamespaceAndFilename(
        shape.getId().getNamespace(),
        filename
      )
    )
      .definitionFile(
        getSymbolDefinitionFilePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
      .build();
  }

  /**
   * Override Smithy-Python to support namespaces in other modules.
   * @param target
   * @return
   */
  @Override
  protected boolean targetRequiresDictHelpers(Shape target) {
    // Do not generate dict helpers for a shape in another namespace
    // (Don't generate *anything* for a shape in another namespace)
    if (!target.getId().getNamespace().equals(service.getId().getNamespace())) {
      return false;
      // Don't generate dict helpers for a shape with a ReferenceTrait
      // This can cause circular import issues
    } else if (target.hasTrait(ReferenceTrait.class)) {
      return false;
    } else {
      return super.targetRequiresDictHelpers(target);
    }
  }

  /**
   * Override Smithy-Python to support namespaces in other modules.
   * @param target
   * @return
   */
  @Override
  public Symbol memberShape(MemberShape shape) {
    var container = model.expectShape(shape.getContainer());
    if (container.isUnionShape()) {
      // Union members, unlike other shape members, have types generated for them.
      var containerSymbol = container.accept(this);
      var name =
        containerSymbol.getName() +
        StringUtils.capitalize(shape.getMemberName());
      String filename = "models";
      return createSymbolBuilder(
        shape,
        name,
        getSymbolNamespacePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
        .definitionFile(
          getSymbolDefinitionFilePathForNamespaceAndFilename(
            shape.getId().getNamespace(),
            filename
          )
        )
        .build();
    }
    Shape targetShape = model
      .getShape(shape.getTarget())
      .orElseThrow(() ->
        new CodegenException("Shape not found: " + shape.getTarget())
      );
    return toSymbol(targetShape);
  }

  /**
   * Override Smithy-Python to support namespaces in other modules.
   * @param shape
   * @return
   */
  @Override
  public Symbol enumShape(EnumShape shape) {
    var builder = createSymbolBuilder(shape, "str");
    String name = getDefaultShapeName(shape);
    String filename = "models";
    Symbol enumSymbol = createSymbolBuilder(
      shape,
      name,
      getSymbolNamespacePathForNamespaceAndFilename(
        shape.getId().getNamespace(),
        filename
      )
    )
      .definitionFile(
        getSymbolDefinitionFilePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
      .build();

    // We add this enum symbol as a property on a generic string symbol
    // rather than returning the enum symbol directly because we only
    // generate the enum constants for convenience. We actually want
    // to pass around plain strings rather than what is effectively
    // a namespace class.
    builder.putProperty("enumSymbol", escaper.escapeSymbol(shape, enumSymbol));
    return builder.build();
  }

  /**
   * Override Smithy-Python to support namespaces in other modules.
   * @param target
   * @return
   */
  @Override
  public Symbol intEnumShape(IntEnumShape shape) {
    var builder = createSymbolBuilder(shape, "int");
    String name = getDefaultShapeName(shape);
    String filename = "models";
    Symbol enumSymbol = createSymbolBuilder(
      shape,
      name,
      getSymbolNamespacePathForNamespaceAndFilename(
        shape.getId().getNamespace(),
        filename
      )
    )
      .definitionFile(
        getSymbolDefinitionFilePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
      .build();

    // Like string enums, int enums are plain ints when used as members.
    builder.putProperty("enumSymbol", escaper.escapeSymbol(shape, enumSymbol));
    return builder.build();
  }

  /**
   * Override Smithy-Python to support namespaces in other modules.
   * @param target
   * @return
   */
  @Override
  public Symbol unionShape(UnionShape shape) {
    String name = getDefaultShapeName(shape);

    var unknownName = name + "Unknown";
    String filename = "models";
    var unknownSymbol = createSymbolBuilder(
      shape,
      name,
      getSymbolNamespacePathForNamespaceAndFilename(
        shape.getId().getNamespace(),
        filename
      )
    )
      .definitionFile(
        getSymbolDefinitionFilePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
      .build();

    return createSymbolBuilder(
      shape,
      name,
      getSymbolNamespacePathForNamespaceAndFilename(
        shape.getId().getNamespace(),
        filename
      )
    )
      .definitionFile(
        getSymbolDefinitionFilePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
      .putProperty("fromDict", createFromDictFunctionSymbol(shape))
      .putProperty("unknown", unknownSymbol)
      .build();
  }

  /**
   * Override Smithy-Python to support namespaces in other modules.
   * @param shape
   * @return
   */
  @Override
  protected Symbol createAsDictFunctionSymbol(Shape shape) {
    String filename = "models";
    return Symbol
      .builder()
      .name(
        String.format(
          "_%s_as_dict",
          CaseUtils.toSnakeCase(shape.getId().getName())
        )
      )
      .namespace(
        getSymbolNamespacePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        ),
        "."
      )
      .definitionFile(
        getSymbolDefinitionFilePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
      .build();
  }

  /**
   * Override Smithy-Python to support namespaces in other modules.
   * @param shape
   * @return
   */
  @Override
  protected Symbol createFromDictFunctionSymbol(Shape shape) {
    String filename = "models";
    return Symbol
      .builder()
      .name(
        String.format(
          "_%s_from_dict",
          CaseUtils.toSnakeCase(shape.getId().getName())
        )
      )
      .namespace(
        getSymbolNamespacePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        ),
        "."
      )
      .definitionFile(
        getSymbolDefinitionFilePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          filename
        )
      )
      .build();
  }
}
