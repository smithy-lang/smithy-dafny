// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import java.util.Map;
import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.polymorph.smithypython.localservice.extensions.DafnyPythonLocalServiceStructureGenerator;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.LocalServiceToDafnyShapeVisitor;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.TopologicalIndex;
import software.amazon.smithy.model.knowledge.NullableIndex;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.traits.StringTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * Extends the Smithy-Python-generated config.py file by writing a shape for the localService config
 * shape and adding type conversions between it and the Dafny config shape.
 */
public class ConfigFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(
      LocalServiceTrait.class
    );
    final StructureShape configShape = codegenContext
      .model()
      .expectShape(localServiceTrait.getConfigId(), StructureShape.class);

    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        codegenContext.settings().getService().getNamespace()
      );
    codegenContext
      .writerDelegator()
      .useFileWriter(
        moduleName + "/config.py",
        "",
        writer -> {
          DafnyNameResolver.importDafnyTypeForShape(
            writer,
            configShape.getId(),
            codegenContext
          );

          writer.write(
            """
            def dafny_config_to_smithy_config(dafny_config) -> $L:
                ""\"
                Converts the provided Dafny shape for this localService's config
                into the corresponding Smithy-modelled shape.
                ""\"
                ${C|}

            def smithy_config_to_dafny_config(smithy_config) -> $L:
                ""\"
                Converts the provided Smithy-modelled shape for this localService's config
                into the corresponding Dafny shape.
                ""\"
                ${C|}
            """,
            configShape.getId().getName(),
            writer.consumer(w ->
              generateDafnyConfigToSmithyConfigFunctionBody(
                configShape,
                codegenContext,
                w
              )
            ),
            DafnyNameResolver.getDafnyTypeForShape(configShape.getId()),
            writer.consumer(w ->
              generateSmithyConfigToDafnyConfigFunctionBody(
                configShape,
                codegenContext,
                w
              )
            )
          );
        }
      );
  }

  /**
   * Generates the body converting the Dafny Config class (from internaldafny code) to the
   * Smithy-modelled Config class defined in this file.
   *
   * @param configShape
   * @param codegenContext
   * @param writer
   */
  private void generateDafnyConfigToSmithyConfigFunctionBody(
    StructureShape configShape,
    GenerationContext codegenContext,
    PythonWriter writer
  ) {
    String output = configShape.accept(
      ShapeVisitorResolver.getToNativeShapeVisitorForShape(
        configShape,
        codegenContext,
        "dafny_config",
        writer
      )
    );
    writer.write("return " + output);
  }

  /**
   * Generates the body converting the Smithy-modelled Config class defined in this file to the
   * Dafny Config class.
   *
   * @param configShape
   * @param codegenContext
   * @param writer
   */
  private void generateSmithyConfigToDafnyConfigFunctionBody(
    StructureShape configShape,
    GenerationContext codegenContext,
    PythonWriter writer
  ) {
    String output = configShape.accept(
      new LocalServiceToDafnyShapeVisitor(
        codegenContext,
        "smithy_config",
        writer
      )
    );
    writer.write("return " + output);
  }
}
