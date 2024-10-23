package software.amazon.polymorph.smithygo.codegen;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.SimpleShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.StreamingTrait;

public class UnionGenerator {

  public static final String UNKNOWN_MEMBER_NAME = "UnknownUnionMember";

  private final Model model;
  private final SymbolProvider symbolProvider;
  private final UnionShape shape;
  private final boolean isEventStream;

  public UnionGenerator(
    Model model,
    SymbolProvider symbolProvider,
    UnionShape shape
  ) {
    this.model = model;
    this.symbolProvider = symbolProvider;
    this.shape = shape;
    this.isEventStream = StreamingTrait.isEventStream(shape);
  }

  /**
   * Generates the Go type definitions for the UnionShape.
   *
   * @param writer the writer
   */
  public void generateUnion(GoWriter writer) {
    Symbol symbol = symbolProvider.toSymbol(shape);
    Collection<MemberShape> memberShapes = shape
      .getAllMembers()
      .values()
      .stream()
      .filter(memberShape -> !isEventStreamErrorMember(memberShape))
      .collect(Collectors.toCollection(TreeSet::new));

    memberShapes
      .stream()
      .map(symbolProvider::toMemberName)
      .forEach(name -> {
        writer.write("//  " + name);
      });
    writer
      .openBlock(
        "type $L interface {",
        "}",
        symbol.getName(),
        () -> {
          writer.write("is$L()", symbol.getName());
        }
      )
      .write("");

    // Create structs for each member that satisfy the interface.
    for (MemberShape member : memberShapes) {
      Symbol memberSymbol = symbolProvider.toSymbol(member);
      String exportedMemberName = symbolProvider.toMemberName(member);
      Shape target = model.expectShape(member.getTarget());

      writer.openBlock(
        "type $L struct {",
        "}",
        exportedMemberName,
        () -> {
          // Union members can't have null values, so for simple shapes we don't
          // use pointers. We have to use pointers for complex shapes since,
          // for example, we could still have a map that's empty or which has
          // null values.
          if (target instanceof SimpleShape) {
            writer.write("Value $T", memberSymbol);
          } else {
            // Handling smithy-dafny Reference Trait begins
            var namespace = SmithyNameResolver.smithyTypesNamespace(target);
            var newMemberSymbol = memberSymbol;
            if (target.hasTrait(ReferenceTrait.class)) {
              newMemberSymbol =
                newMemberSymbol.getProperty("Referred", Symbol.class).get();
              var refShape = target.expectTrait(ReferenceTrait.class);
              if (refShape.isService()) {
                namespace =
                  SmithyNameResolver.shapeNamespace(
                    model.expectShape(refShape.getReferentId())
                  );
              }
              if (
                !member
                  .toShapeId()
                  .getNamespace()
                  .equals(refShape.getReferentId().getNamespace())
              ) {
                writer.addImportFromModule(
                  SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                    refShape.getReferentId().getNamespace()
                  ),
                  namespace
                );
              }
            } else {
              if (
                !member
                  .toShapeId()
                  .getNamespace()
                  .equals(target.toShapeId().getNamespace()) &&
                !target.toShapeId().getNamespace().startsWith("smithy") &&
                target.asStructureShape().isPresent()
              ) {
                writer.addImportFromModule(
                  SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                    target.toShapeId().getNamespace()
                  ),
                  namespace
                );
              }
            }
            // Handling smithy-dafny Reference Trait ends.
            writer.write("Value $P", newMemberSymbol);
          }
          writer.write("");
        }
      );

      writer.write(
        "func (*$L) is$L() {}",
        exportedMemberName,
        symbol.getName()
      );
    }
  }

  private boolean isEventStreamErrorMember(MemberShape memberShape) {
    return (
      isEventStream &&
      memberShape.getMemberTrait(model, ErrorTrait.class).isPresent()
    );
  }

  /**
   * Generates a struct for unknown union values that applies to every union in the given set.
   *
   * @param writer         The writer to write the union to.
   * @param unions         A set of unions whose interfaces the union should apply to.
   * @param symbolProvider A symbol provider used to get the symbols for the unions.
   */
  public static void generateUnknownUnion(
    final GoWriter writer,
    final Collection<UnionShape> unions,
    final SymbolProvider symbolProvider
  ) {
    writer.openBlock(
      "type $L struct {",
      "}",
      UNKNOWN_MEMBER_NAME,
      () -> {
        // The tag (member) name received over the wire.
        writer.write("Tag string");
        // The value received.
        writer.write("Value []byte");
        writer.write("");
      }
    );

    for (UnionShape union : unions) {
      writer.write(
        "func (*$L) is$L() {}",
        UNKNOWN_MEMBER_NAME,
        symbolProvider.toSymbol(union).getName()
      );
    }
  }
}
