package software.amazon.polymorph.smithypython.awssdk.extensions;

import static java.lang.String.format;

import software.amazon.polymorph.smithypython.awssdk.AwsSdkCodegenConstants;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.extensions.DafnyPythonLocalServiceSymbolVisitor;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.PythonSettings;

/**
 * SymbolVisitor for wrapped localService codegen. Overrides the generated file for codegen to
 * something that is immediately deleted. Smithy ALWAYS writes visited symbols to a file. For AWS
 * SDK codegen, we do NOT want to write visited symbols to a file, since boto3 does not use these
 * visited symbols. It is very, very difficult to change this writing behavior without rewriting
 * Smithy logic in addition to Smithy-Python specific logic. I have tried some workarounds like
 * deleting writers or writing to /dev/null but these were not fruitful. This workaround dumps any
 * visited symbols into a file whose name will never be used and deletes this file as part of its
 * Smithy codegen plugin.
 */
public class DafnyPythonAwsSdkSymbolVisitor
  extends DafnyPythonLocalServiceSymbolVisitor {

  public DafnyPythonAwsSdkSymbolVisitor(Model model, PythonSettings settings) {
    super(model, settings);
  }

  /**
   * Path to the overridden file that is deleted for wrapped services.
   *
   * @param namespace
   * @return
   */
  @Override
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

    return format(
      "%s/%s.py",
      directoryFilePath,
      AwsSdkCodegenConstants.AWS_SDK_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME
    );
  }

  @Override
  public Symbol unionShape(UnionShape shape) {
    // boto3 doesn't model unions like localServices do.
    // Any unions are dictionaries.
    System.out.println("ABC");
    System.out.println(shape.getType());
    String name = "dict[str, ABC]";
    return createSymbolBuilder(
      shape,
      name,
      ""
    )
      .definitionFile(
        getSymbolDefinitionFilePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          ""
        )
      )
      .build();
  }

  @Override
  public Symbol structureShape(StructureShape shape) {
    // boto3 doesn't model structures like localServices do.
    // Any structures are dictionaries.
    String name = "dict[str, Any]";
    return createSymbolBuilder(
      shape,
      name,
      ""
    )
      .definitionFile(
        getSymbolDefinitionFilePathForNamespaceAndFilename(
          shape.getId().getNamespace(),
          ""
        )
      )
      .build();
  }
}
