package software.amazon.polymorph.smithyrust.generator;


import software.amazon.polymorph.utils.TokenTree;

import java.nio.file.Path;

public record RustFile(Path path, TokenTree content) {
}
