package software.amazon.polymorph.smithygo.utils;

import software.amazon.polymorph.smithygo.codegen.SymbolUtils;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.NeighborProviderIndex;
import software.amazon.smithy.model.neighbor.NeighborProvider;
import software.amazon.smithy.model.neighbor.Relationship;
import software.amazon.smithy.model.neighbor.RelationshipType;
import software.amazon.smithy.model.shapes.Shape;

public class GoCodegenUtils {

  public static String getType(
    final Symbol symbol,
    final ServiceTrait serviceTrait
  ) {
    if (
      symbol.getProperty(SymbolUtils.GO_ELEMENT_TYPE, Symbol.class).isEmpty()
    ) {
      return SmithyNameResolver.getSmithyTypeAws(serviceTrait, symbol, true);
    }
    final var type = getType(
      symbol.expectProperty(SymbolUtils.GO_ELEMENT_TYPE, Symbol.class),
      serviceTrait
    );
    if (symbol.getProperty(SymbolUtils.GO_MAP).isPresent()) {
      return "map[string]" + type;
    }
    if (symbol.getProperty(SymbolUtils.GO_SLICE).isPresent()) {
      return "[]" + type;
    }
    throw new RuntimeException("Failed to determine shape type");
  }

  public static String getType(final Symbol symbol, final Shape shape) {
    if (
      symbol.getProperty(SymbolUtils.GO_ELEMENT_TYPE, Symbol.class).isEmpty()
    ) {
      return SmithyNameResolver.getSmithyType(shape, symbol);
    }
    var type = getType(
      symbol.expectProperty(SymbolUtils.GO_ELEMENT_TYPE, Symbol.class),
      shape
    );
    if (symbol.getProperty(SymbolUtils.GO_MAP).isPresent()) {
      type = "map[string]" + type;
    }
    if (symbol.getProperty(SymbolUtils.GO_SLICE).isPresent()) {
      type = "[]" + type;
    }
    return type;
  }

  public static Symbol getRootSymbol(final Symbol symbol) {
    if (
      symbol.getProperty(SymbolUtils.GO_ELEMENT_TYPE, Symbol.class).isEmpty()
    ) {
      return symbol;
    }
    return getRootSymbol(
      symbol.expectProperty(SymbolUtils.GO_ELEMENT_TYPE, Symbol.class)
    );
  }

  public static boolean isOperationStruct(
    final Model model,
    final Shape shape
  ) {
    final NeighborProvider provider = NeighborProviderIndex
      .of(model)
      .getReverseProvider();
    for (Relationship relationship : provider.getNeighbors(shape)) {
      final RelationshipType relationshipType =
        relationship.getRelationshipType();
      if (
        relationshipType == RelationshipType.INPUT ||
        relationshipType == RelationshipType.OUTPUT
      ) {
        return true;
      }
    }

    return false;
  }
}
