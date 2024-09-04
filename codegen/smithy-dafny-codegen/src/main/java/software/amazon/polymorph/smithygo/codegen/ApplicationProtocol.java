package software.amazon.polymorph.smithygo.codegen;

import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.utils.SmithyUnstableApi;

/**
 * Represents the resolves {@link Symbol}s and references for an
 * application protocol (e.g., "http", "mqtt", etc).
 */
@SmithyUnstableApi
public record ApplicationProtocol(
  String name,
  SymbolReference requestType,
  SymbolReference responseType
) {}
