package software.amazon.polymorph.smithygo.codegen;

import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;

import java.math.BigDecimal;
import java.util.Optional;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.SimpleShape;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.StreamingTrait;

// Renders constraint validation
public class ValidationGenerator {

  private final Model model;
  private final SymbolProvider symbolProvider;
  private final GoWriter writer;
  private final CodegenUtils.SortedMembers sortedMembers;

  private static final String LIST_ITEM = "item";
  private static final String MAP_KEY = "key";
  private static final String MAP_VALUE = "value";
  private static final String UNION_DATASOURCE = "unionType.Value";

  public ValidationGenerator(
    final Model model,
    final SymbolProvider symbolProvider,
    final GoWriter writer
  ) {
    this.model = model;
    this.symbolProvider = symbolProvider;
    this.writer = writer;
    this.sortedMembers = new CodegenUtils.SortedMembers(symbolProvider);
  }

  public void renderValidator(
    final Shape shape,
    final boolean isInputStructure
  ) {
    Symbol symbol = symbolProvider.toSymbol(shape);
    writer.openBlock("func (input $L) Validate() (error) {", symbol.getName());
    renderValidatorHelper(shape, isInputStructure, "input");
    writer.write("return nil");
    writer.closeBlock("}").write("");
  }

  private void renderValidatorHelper(
    final Shape containerShape,
    final boolean isInputStructure,
    final String dataSource
  ) {
    containerShape
      .getAllMembers()
      .values()
      .stream()
      .filter(memberShape -> !StreamingTrait.isEventStream(model, memberShape))
      .sorted(sortedMembers)
      .forEach(member -> {
        String memberName;
        if (
          containerShape.isListShape() || containerShape.isMapShape()
        ) memberName = dataSource; else memberName =
          dataSource + "." + symbolProvider.toMemberName(member);
        renderValidatorForEachShape(
          model.expectShape(member.getTarget()),
          member,
          isInputStructure,
          memberName
        );
      });
  }

  private void renderValidatorForEachShape(
    final Shape currentShape,
    final MemberShape memberShape,
    final boolean isInputStructure,
    final String dataSource
  ) {
    Symbol symbol = symbolProvider.toSymbol(currentShape);
    if (isInputStructure) {
      symbol =
        symbol
          .getProperty(SymbolUtils.INPUT_VARIANT, Symbol.class)
          .orElse(symbol);
    }
    if (currentShape.hasTrait(ReferenceTrait.class)) {
      symbol = symbol.getProperty("Referred", Symbol.class).get();
    }
    String pointableString = "";
    if (
      !(dataSource.equals(LIST_ITEM) ||
        dataSource.equals(MAP_KEY) ||
        dataSource.equals(MAP_VALUE) ||
        (dataSource.equals(UNION_DATASOURCE) &&
          currentShape instanceof SimpleShape))
    ) {
      if (
        (boolean) symbol.getProperty(POINTABLE, Boolean.class).orElse(false) &&
        memberShape.isOptional()
      ) {
        pointableString = "*";
      }
    }
    if (currentShape.hasTrait(RangeTrait.class)) {
      addRangeCheck(currentShape, dataSource, pointableString);
    }
    if (currentShape.hasTrait(LengthTrait.class)) {
      addLengthCheck(currentShape, dataSource, pointableString);
    }
    if (currentShape.hasTrait(RequiredTrait.class)) {
      addRequiredCheck(symbol, currentShape, dataSource);
    }
    if (currentShape.hasTrait(DafnyUtf8BytesTrait.class)) {
      addUTFCheck(currentShape, dataSource, pointableString);
    }
    // Broke list and map into two different if else because for _, item := range %s looked good for list
    // And for key, value := range %s looked good for map
    if (currentShape.isListShape()) {
      writer.write(
        """
        for _, %s := range %s {
            // To avoid declared and not used error for shapes which does not need validation check
            _ = item
        """.formatted(LIST_ITEM, dataSource)
      );
      renderValidatorHelper(currentShape, false, LIST_ITEM);
      writer.write(
        """
        }
        """
      );
    } else if (currentShape.isMapShape()) {
      writer.write(
        """
        for %s, %s := range %s {
            // To avoid declared and not used error for shapes which does not need validation check
            _ = key
            _ = value
        """.formatted(MAP_KEY, MAP_VALUE, dataSource)
      );
      renderValidatorHelper(currentShape, false, MAP_KEY);
      renderValidatorHelper(currentShape, false, MAP_VALUE);
      writer.write(
        """
            }
        """
      );
    } else if (currentShape.isUnionShape()) {
      writer.write(
        """
        switch unionType := %s.(type) {
            """.formatted(dataSource)
      );
      for (var memberInUnion : currentShape.getAllMembers().values()) {
        writer.write(
          """
          case *%s:
          """.formatted(symbolProvider.toMemberName(memberInUnion))
        );

        renderValidatorForEachShape(
          model.expectShape(memberInUnion.getTarget()),
          memberInUnion,
          false,
          "unionType.Value"
        );
      }
      writer.write(
        """
                // Default case should not be reached.
                default:
                    // To avoid used and not used error when nothing to validate
                    _ = unionType
        panic("Unhandled union type")
                }
                    """
      );
    } else {
      renderValidatorHelper(currentShape, isInputStructure, dataSource);
    }
  }

  private void addRangeCheck(
    final Shape currentShape,
    final String dataSource,
    final String pointableString
  ) {
    StringBuilder rangeCheck = new StringBuilder();
    RangeTrait rangeTraitShape = currentShape.expectTrait(RangeTrait.class);
    Optional<BigDecimal> min = rangeTraitShape.getMin();
    Optional<BigDecimal> max = rangeTraitShape.getMax();
    if (pointableString.equals("*")) {
      rangeCheck.append(
        """
            if (%s != nil) {
        """.formatted(dataSource)
      );
    }
    if (min.isPresent()) {
      rangeCheck.append(
        """
        if (%s%s < %s) {
            return fmt.Errorf(\"%s has a minimum of %s but has the value of %%d.\", %s%s)
        }
        """.formatted(
            pointableString,
            dataSource,
            min.get().toString(),
            currentShape.getId().getName(),
            min.get().toString(),
            pointableString,
            dataSource
          )
      );
    }
    if (max.isPresent()) {
      rangeCheck.append(
        """
        if (%s%s > %s) {
            return fmt.Errorf(\"%s has a maximum of %s but has the value of %%d.\", %s%s)
        }
        """.formatted(
            pointableString,
            dataSource,
            max.get().toString(),
            currentShape.getId().getName(),
            max.get().toString(),
            pointableString,
            dataSource
          )
      );
    }
    if (pointableString.equals("*")) {
      rangeCheck.append(
        """
        }
        """
      );
    }
    writer.write(rangeCheck);
  }

  private void addLengthCheck(
    final Shape currentShape,
    final String dataSource,
    final String pointableString
  ) {
    StringBuilder lengthCheck = new StringBuilder();
    LengthTrait lengthTraitShape = currentShape.expectTrait(LengthTrait.class);
    Optional<Long> min = lengthTraitShape.getMin();
    Optional<Long> max = lengthTraitShape.getMax();
    if (pointableString.equals("*")) {
      lengthCheck.append(
        """
            if (%s != nil) {
        """.formatted(dataSource)
      );
    }
    if (min.isPresent()) {
      if (currentShape.hasTrait(DafnyUtf8BytesTrait.class)) {
        lengthCheck.append(
          """
          if (utf8.RuneCountInString(%s%s) < %s) {
              return fmt.Errorf(\"%s has a minimum length of %s but has the length of %%d.\", utf8.RuneCountInString(%s%s))
          }
          """.formatted(
              pointableString,
              dataSource,
              min.get().toString(),
              currentShape.getId().getName(),
              min.get().toString(),
              pointableString,
              dataSource
            )
        );
      } else {
        lengthCheck.append(
          """
          if (len(%s%s) < %s) {
              return fmt.Errorf(\"%s has a minimum length of %s but has the length of %%d.\", len(%s%s))
          }
          """.formatted(
              pointableString,
              dataSource,
              min.get().toString(),
              currentShape.getId().getName(),
              min.get().toString(),
              pointableString,
              dataSource
            )
        );
      }
    }
    if (max.isPresent()) {
      if (currentShape.hasTrait(DafnyUtf8BytesTrait.class)) {
        lengthCheck.append(
          """
          if (utf8.RuneCountInString(%s%s) > %s) {
              return fmt.Errorf(\"%s has a maximum length of %s but has the length of %%d.\", utf8.RuneCountInString(%s%s))
          }
          """.formatted(
              pointableString,
              dataSource,
              max.get().toString(),
              currentShape.getId().getName(),
              max.get().toString(),
              pointableString,
              dataSource
            )
        );
      } else {
        lengthCheck.append(
          """
          if (len(%s%s) > %s) {
              return fmt.Errorf(\"%s has a maximum length of %s but has the length of %%d.\", len(%s%s))
          }
          """.formatted(
              pointableString,
              dataSource,
              max.get().toString(),
              currentShape.getId().getName(),
              max.get().toString(),
              pointableString,
              dataSource
            )
        );
      }
    }
    if (pointableString.equals("*")) {
      lengthCheck.append(
        """
        }
        """
      );
    }
    writer.write(lengthCheck);
  }

  private void addRequiredCheck(
    final Symbol memberSymbol,
    final Shape currentShape,
    final String dataSource
  ) {
    StringBuilder RequiredCheck = new StringBuilder();
    if (
      memberSymbol.getProperty(POINTABLE).isPresent() &&
      (boolean) memberSymbol.getProperty(POINTABLE).get()
    ) RequiredCheck.append(
      """
      if ( %s == nil ) {
          return fmt.Errorf(\"%s is required but has a nil value.\")
      }
      """.formatted(dataSource, dataSource)
    );
    writer.write(RequiredCheck);
  }

  private void addUTFCheck(
    final Shape currentShape,
    final String dataSource,
    final String pointableString
  ) {
    StringBuilder UTFCheck = new StringBuilder();
    if (pointableString.equals("*")) {
      UTFCheck.append(
        """
            if ( %s != nil ) {
        """.formatted(dataSource)
      );
    }
    UTFCheck.append(
      """
      if (!utf8.ValidString(%s%s)) {
          return fmt.Errorf(\"Invalid UTF bytes %%s \", %s%s)
      }
      """.formatted(pointableString, dataSource, pointableString, dataSource)
    );
    if (pointableString.equals("*")) {
      UTFCheck.append(
        """
        }
        """
      );
    }
    writer.write(UTFCheck);
  }
}
