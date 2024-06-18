// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.utils;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.smithy.utils.IoUtils;
import software.amazon.smithy.utils.SimpleCodeWriter;

public class IOUtils {

  private static final Logger LOGGER = LoggerFactory.getLogger(IOUtils.class);

  public static void writeToFile(final String text, final File file) {
    try {
      final FileWriter fileWriter = new FileWriter(file);
      fileWriter.write(text);
      if (!text.endsWith("\n")) {
        fileWriter.write("\n");
      }
      fileWriter.close();
    } catch (IOException e) {
      LOGGER.error("Could not write to file {}", file);
      e.printStackTrace();
    }
  }

  private static final String COPYRIGHT_HEADER =
    """
    // Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
    // SPDX-License-Identifier: Apache-2.0
    """;

  private static final String GENERATED_HEADER =
    """
    // Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
    """;

  public static void writeTokenTreesIntoDir(
    final Map<Path, TokenTree> tokenTreeMap,
    final Path outputDir
  ) {
    for (Map.Entry<Path, TokenTree> entry : tokenTreeMap.entrySet()) {
      Path localPath = entry.getKey();
      TokenTree tokens = entry.getValue();
      final Path outputPath = Path.of(
        outputDir.toString(),
        localPath.toString()
      );
      try {
        Files.createDirectories(outputPath.getParent());
        final String content =
          COPYRIGHT_HEADER + GENERATED_HEADER + tokens.toString();
        writeToFile(content, outputPath.toFile());
      } catch (IOException e) {
        e.printStackTrace();
      }
    }
  }

  /**
   * Evaluate a simple template as a resource under "/templates/<templatePath>"
   * and then write it to "<rootPath>/<templatePath>".
   * The template path is also evaluated as a template,
   * so the path can be customized by parameter values as well.
   *
   * Template parameters with no value bound become "",
   * so they can also be used to provide more than one template
   * for the same file.
   *
   * See also {@link #evalTemplate(String, Map)}.
   */
  public static void writeTemplatedFile(
    Class<?> klass,
    Path rootPath,
    String templatePath,
    String templateOutputPath,
    Map<String, String> parameters
  ) {
    String content = IoUtils.readUtf8Resource(
      klass,
      "/templates/" + templatePath
    );

    content = evalTemplate(content, parameters);
    templateOutputPath = evalTemplate(templateOutputPath, parameters);

    Path outputPath = rootPath.resolve(templateOutputPath);
    try {
      Files.createDirectories(outputPath.getParent());
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }

    IOUtils.writeToFile(content, outputPath.toFile());
    LOGGER.info("Additional templated content written to {}", outputPath);
  }

  /**
   * Evaluate a simple template using a {@link SimpleCodeWriter}.
   * See {@link software.amazon.smithy.utils.AbstractCodeWriter} for documentation
   * on the templating syntax.
   */
  public static String evalTemplate(
    String template,
    Map<String, String> context
  ) {
    SimpleCodeWriter writer = new SimpleCodeWriter()
      .disableNewlines()
      .insertTrailingNewline(false);
    for (Map.Entry<String, String> entry : context.entrySet()) {
      writer.putContext(entry.getKey(), entry.getValue());
    }
    writer.write(template);
    return writer.toString();
  }
}
