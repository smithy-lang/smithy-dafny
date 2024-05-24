// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.utils;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.smithy.utils.IoUtils;

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

  public static void writeTemplatedFile(Path rootPath, String templatePath, Map<String, String> parameters) {
    String content = IoUtils.readUtf8Resource(
            IOUtils.class.getClass(),
            "/templates/" + templatePath
    );

    for (Map.Entry<String, String> entry : parameters.entrySet()) {
      content = content.replace(entry.getKey(), entry.getValue());
    }
    for (Map.Entry<String, String> entry : parameters.entrySet()) {
      templatePath = templatePath.replace(entry.getKey(), entry.getValue());
    }

    IOUtils.writeToFile(
            content,
            rootPath.resolve(templatePath).toFile()
    );
  }
}
