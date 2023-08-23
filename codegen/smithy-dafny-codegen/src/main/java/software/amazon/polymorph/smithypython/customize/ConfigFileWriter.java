package software.amazon.polymorph.smithypython.customize;

import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithypython.shapevisitor.SmithyToDafnyShapeVisitor;
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
          DafnyNameResolver.importDafnyTypeForShape(writer, configShape.getId());

          writer.write(
              """
              class $L(Config):
                  # TODO: Add types to Config members
                  ${C|}
                  
                  def __init__(self, ${C|}):
                      super().__init__()
                      ${C|}
                    
              def dafny_config_to_smithy_config(dafny_config) -> $L:
                  ${C|}
                  
              def smithy_config_to_dafny_config(smithy_config) -> $L:
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

  private void generateConfigConstructorParameters(
      StructureShape configShape, GenerationContext codegenContext, PythonWriter writer) {
    Map<String, MemberShape> memberShapeSet = configShape.getAllMembers();
    for (String memberName : memberShapeSet.keySet()) {
      // TODO: Instead of `Any`, map the targetShape.getType Smithy type to the Python type
      writer.writeInline("$L, ", CaseUtils.toSnakeCase(memberName));
    }
  }

  private void generateConfigConstructorFieldAssignments(
      StructureShape configShape, GenerationContext codegenContext, PythonWriter writer) {
    Map<String, MemberShape> memberShapeSet = configShape.getAllMembers();
    for (String memberName : memberShapeSet.keySet()) {
      // TODO: Instead of `Any`, map the targetShape.getType Smithy type to the Python type
      writer.write("self.$L = $L", CaseUtils.toSnakeCase(memberName), CaseUtils.toSnakeCase(memberName));
    }
  }

  private void generateDafnyConfigToSmithyConfigFunctionBody(
      StructureShape configShape, GenerationContext codegenContext, PythonWriter writer) {
    String output = configShape.accept(new DafnyToSmithyShapeVisitor(
        codegenContext,
        "dafny_config",
        writer,
        true
    ));
    writer.write("return " + output);
  }

  private void generateSmithyConfigToDafnyConfigFunctionBody(
      StructureShape configShape, GenerationContext codegenContext, PythonWriter writer) {
    String output = configShape.accept(new SmithyToDafnyShapeVisitor(
        codegenContext,
        "smithy_config",
        writer,
        true
    ));
    writer.write("return " + output);
  }

}
