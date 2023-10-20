package software.amazon.polymorph.smithypython.awssdk.extensions;

import java.nio.file.Path;
import java.util.logging.Logger;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.directed.CustomizeDirective;
import software.amazon.smithy.codegen.core.directed.GenerateServiceDirective;
import software.amazon.smithy.python.codegen.CodegenUtils;
import software.amazon.smithy.python.codegen.DirectedPythonCodegen;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;

/**
 * DirectedCodegen for Dafny Python AWS SDK models.
 * This overrides DirectedPythonCodegen to
 * 1) Not generate a Smithy client (nor its serialize/deserialize bodies, client config, etc.)
 * 2) Remove extraneous generated files (TODO-Python: Consider rewriting SymbolVisitor to avoid this)
 * AWS SDK generation does NOT involve generating a Smithy client;
 *   it will only generate a shim wrapping boto3.
 */
public class DirectedDafnyPythonAwsSdkCodegen extends DirectedPythonCodegen {

  private static final Logger LOGGER = Logger.getLogger(DirectedDafnyPythonAwsSdkCodegen.class.getName());

  /**
   * Do NOT generate any service config code for Dafny Python AWS SDKs (i.e. `config.py`).
   * Override DirectedPythonCodegen to block any service config code generation.
   * @param directive Directive to perform.
   */
  @Override
  public void customizeBeforeShapeGeneration(
      CustomizeDirective<GenerationContext, PythonSettings> directive) { }

  /**
   * Do NOT generate any service code for Dafny Python AWS SDKs.
   * Override DirectedPythonCodegen to block any service code generation.
   * In addition to not writing any service code (i.e. not writing `client.py`),
   *   this also blocks writing `serialize.py` and `deserialize.py`.
   * @param directive Directive to perform.
   */
  @Override
  public void generateService(
      GenerateServiceDirective<GenerationContext, PythonSettings> directive) { }

  /**
   * Call `DirectedPythonCodegen.customizeAfterIntegrations`,
   *   then remove `models.py` and `errors.py`.
   * The CodegenDirector will invoke this method after shape generation.
   * @param directive Directive to perform.
   */
  @Override
  public void customizeAfterIntegrations(CustomizeDirective<GenerationContext, PythonSettings> directive) {
    // DirectedPythonCodegen's customizeAfterIntegrations implementation SHOULD run first;
    //   its implementation writes all files by flushing its writers;
    //   this implementation removes some of those files.
    super.customizeAfterIntegrations(directive);

    FileManifest fileManifest = directive.fileManifest();
    Path generationPath = Path.of(
        fileManifest.getBaseDir() + "/" + directive.context().settings().getModuleName());

    // models.py and errors.py are written to from DEEP within Smithy-Python.
    // Any time a SymbolVisitor encounters a complex shape (structure, union. etc.)
    //   it will automatically write a shape definition for that shape in these files.
    // This is in contrast to `serialize`, `deserialize`, `config`, and `client`,
    //   for which DirectedDafnyPythonAwsSdkCodegen does NOT generate any code
    //   by overriding DirectedPythonCodegen in its method above.
    // If we wish to avoid such a blase removal of these files,
    //   we should consider a deeper rewrite of SymbolVisitor interactions.
    try {
      LOGGER.info("Attempting to remove models.py");
      CodegenUtils.runCommand("rm models.py", generationPath).strip();
    } catch (CodegenException e) {
      LOGGER.warning("Unable to remove models.py: " + e);
    }

    try {
      LOGGER.info("Attempting to remove errors.py");
      CodegenUtils.runCommand("rm errors.py", generationPath).strip();
    } catch (CodegenException e) {
      LOGGER.warning("Unable to remove errors.py:" + e);
    }
  }
}
