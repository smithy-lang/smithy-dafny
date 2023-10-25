package software.amazon.polymorph.smithypython.localservice.customize;

import java.util.Map;
import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.DafnyToLocalServiceShapeVisitor;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceConfigToDafnyConfigShapeVisitor;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * Extends the Smithy-Python-generated config.py file
 * by writing a shape for the localService config shape
 * and adding type conversions between it and the Dafny config shape.
 */
public class ConfigFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(LocalServiceTrait.class);
    final StructureShape configShape = codegenContext.model().expectShape(localServiceTrait.getConfigId(), StructureShape.class);

    String moduleName = codegenContext.settings().getModuleName();
    codegenContext.writerDelegator()
        .useFileWriter(moduleName + "/config.py", "", writer -> {
          DafnyNameResolver.importDafnyTypeForShape(writer, configShape.getId(), codegenContext);

          writer.write(
              """
              class $L(Config):
                  '''
                  Smithy-modelled localService Config shape for this localService.
                  '''
                  # TODO: Add types to Config members
                  ${C|}
                  
                  def __init__(self, ${C|}):
                      super().__init__()
                      ${C|}
                    
              def dafny_config_to_smithy_config(dafny_config) -> $L:
                  '''
                  Converts the provided Dafny shape for this localService's config
                  into the corresponding Smithy-modelled shape.
                  '''
                  ${C|}
                  
              def smithy_config_to_dafny_config(smithy_config) -> $L:
                  '''
                  Converts the provided Smithy-modelled shape for this localService's config
                  into the corresponding Dafny shape.
                  '''
                  ${C|}
              """,
              configShape.getId().getName(),
              writer.consumer(w -> generateConfigClassFields(configShape, codegenContext, w)),
              writer.consumer(w -> generateConfigConstructorParameters(configShape, codegenContext, w)),
              writer.consumer(w -> generateConfigConstructorFieldAssignments(configShape, codegenContext, w)),
              configShape.getId().getName(),
              writer.consumer(w -> generateDafnyConfigToSmithyConfigFunctionBody(configShape, codegenContext, w)),
              DafnyNameResolver.getDafnyTypeForShape(configShape.getId()),
              writer.consumer(w -> generateSmithyConfigToDafnyConfigFunctionBody(configShape, codegenContext, w))
            );
        });
  }

  /**
   * Generates the members of the Smithy-modelled localService Config shape's class.
   * Called when writing the class.
   * @param configShape
   * @param codegenContext
   * @param writer
   */
  private void generateConfigClassFields(
      StructureShape configShape, GenerationContext codegenContext, PythonWriter writer) {
    Map<String, MemberShape> memberShapeSet = configShape.getAllMembers();
    for (Entry<String, MemberShape> memberShapeEntry : memberShapeSet.entrySet()) {
      String memberName = memberShapeEntry.getKey();
      // TODO: Instead of `Any`, map the targetShape.getType() Smithy type to the Python type
      // Prototype code commented out...
//      MemberShape memberShape = memberShapeEntry.getValue();
//      final Shape targetShape = codegenContext.model().expectShape(memberShape.getTarget());
//      final ShapeType targetShapeType = targetShape.getType();
      writer.write("$L: Any", CaseUtils.toSnakeCase(memberName));
    }
  }

  /**
   * Generates constructor parameters for the localService's Config class.
   * Called when writing parameters for the Config class' constructor (__init__ method).
   * @param configShape
   * @param codegenContext
   * @param writer
   */
  private void generateConfigConstructorParameters(
      StructureShape configShape, GenerationContext codegenContext, PythonWriter writer) {
    Map<String, MemberShape> memberShapeSet = configShape.getAllMembers();
    for (String memberName : memberShapeSet.keySet()) {
      // TODO: Instead of `Any`, map the targetShape.getType Smithy type to the Python type
      writer.writeInline("$L, ", CaseUtils.toSnakeCase(memberName));
    }
  }

  /**
   * Generates assignments to fields for the localService's Config class.
   * Called when writing the Config class' constructor.
   * @param configShape
   * @param codegenContext
   * @param writer
   */
  private void generateConfigConstructorFieldAssignments(
      StructureShape configShape, GenerationContext codegenContext, PythonWriter writer) {
    Map<String, MemberShape> memberShapeSet = configShape.getAllMembers();
    for (String memberName : memberShapeSet.keySet()) {
      // TODO: Instead of `Any`, map the targetShape.getType Smithy type to the Python type
      writer.write("self.$L = $L", CaseUtils.toSnakeCase(memberName), CaseUtils.toSnakeCase(memberName));
    }
  }

  /**
   * Generates the body converting the Dafny Config class (from internaldafny code)
   *   to the Smithy-modelled Config class defined in this file.
   * @param configShape
   * @param codegenContext
   * @param writer
   */
  private void generateDafnyConfigToSmithyConfigFunctionBody(
      StructureShape configShape, GenerationContext codegenContext, PythonWriter writer) {
    String output = configShape.accept(new DafnyToLocalServiceShapeVisitor(
        codegenContext,
        "dafny_config",
        writer
    ));
    writer.writeComment("Import dafny_to_smithy at runtime to prevent introducing circular dependency on config file.");
    writer.write("$L",
        "".equals(SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
            configShape.getId().getNamespace(), codegenContext
        ))
        ? "from .dafny_to_smithy import %1$s".formatted(
            SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(
                configShape,
                codegenContext
            ))
        : "import %1$s.dafny_to_smithy".formatted(SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
            configShape.getId().getNamespace(), codegenContext
        ))
    );
    writer.write("return " + output);
  }

  /**
   * Generates the body converting the Smithy-modelled Config class defined in this file
   *   to the Dafny Config class.
   * @param configShape
   * @param codegenContext
   * @param writer
   */
  private void generateSmithyConfigToDafnyConfigFunctionBody(
      StructureShape configShape, GenerationContext codegenContext, PythonWriter writer) {
    // Dafny-generated config shapes contain a piece of unmodelled behavior,
    //   which is that every config member is required.
    //
    String output = configShape.accept(new LocalServiceConfigToDafnyConfigShapeVisitor(
        codegenContext,
        "smithy_config",
        writer
    ));
    writer.write("return smithy_to_dafny." + output);
  }

}
