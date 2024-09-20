package software.amazon.polymorph.smithyrust.generator;

import java.nio.file.Path;
import software.amazon.polymorph.utils.TokenTree;

/**
 * Simple record to pair the content of a file with its target path,
 * inspired by (but much simpler than) {@link com.squareup.javapoet.JavaFile}.
 */
public record RustFile(Path path, TokenTree content) {}
