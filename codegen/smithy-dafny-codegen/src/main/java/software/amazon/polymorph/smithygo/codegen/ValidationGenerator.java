package software.amazon.polymorph.smithygo.codegen;

import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import software.amazon.polymorph.smithygo.codegen.knowledge.GoPointableIndex;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.StreamingTrait;
import software.amazon.polymorph.smithygo.utils.GoCodegenUtils;

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
  private static final String CHECK_AND_RETURN_ERROR =
    """
    if %s != nil {
        return %s
    }
    """;
  private static final Map<MemberShape, String> validationFuncMap =
    new HashMap<>();
  private static final Map<MemberShape, String> validationFuncInputTypeMap =
    new HashMap<>();

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

  public static String funcNameGenerator(
    final MemberShape memberShape,
    final String suffix
  ) {
    return memberShape
      .getId()
      .toString()
      .replaceAll("[.$#]", "_")
      .concat("_")
      .concat(suffix);
  }

  public void renderValidator(
    final Shape shape,
    final boolean isInputStructure
  ) {
    Symbol symbol = symbolProvider.toSymbol(shape);
    writer.openBlock("func (input $L) Validate() (error) {", symbol.getName());
    writer.write(
      renderValidatorHelper(
        shape,
        isInputStructure,
        "input",
        new StringBuilder()
      )
    );
    writer.write("return nil");
    writer.closeBlock("}").write("");
    writeFuncValidations(symbol);
  }

  public void writeFuncValidations(final Symbol symbol) {
    for (final MemberShape key : validationFuncMap.keySet()) {
      String inputType = "";
      if (validationFuncInputTypeMap.containsKey(key)) {
        inputType = "Value ".concat(validationFuncInputTypeMap.get(key));
      }
      writer.openBlock(
        "func (input $L) $L($L) (error) {",
        symbol.getName(),
        funcNameGenerator(key, "validate"),
        inputType
      );
      writer.write(validationFuncMap.get(key));
      writer.write("return nil");
      writer.closeBlock("}");
    }
    validationFuncMap.clear();
  }

  private StringBuilder renderValidatorHelper(
    final Shape containerShape,
    final boolean isInputStructure,
    final String dataSource,
    final StringBuilder validationCode
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
        ) {
          memberName = dataSource;
        } else {
          memberName = dataSource.concat(".").concat(symbolProvider.toMemberName(member));
        }
        renderValidatorForEachShape(
          model.expectShape(member.getTarget()),
          member,
          isInputStructure,
          memberName,
          validationCode
        );
      });
    return validationCode;
  }

  private void renderValidatorForEachShape(
    final Shape currentShape,
    final MemberShape memberShape,
    final boolean isInputStructure,
    String dataSource,
    final StringBuilder validationCode
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
    validationCode.append(
      addRangeCheck(memberShape, dataSource, pointableString)
    );
    validationCode.append(
      addLengthCheck(memberShape, dataSource, pointableString)
    );
    validationCode.append(addRequiredCheck(symbol, memberShape, dataSource));
    validationCode.append(
      addUTFCheck(memberShape, dataSource, pointableString)
    );
    // Broke list and map into two different if else because for _, item := range %s looked good for list
    // And for key, value := range %s looked good for map
    switch (currentShape.getType()) {
      case LIST:
        renderListShape(currentShape.asListShape().orElseThrow(), memberShape, validationCode, dataSource);
        break;
      case MAP:
        renderMapShape(currentShape.asMapShape().orElseThrow(), memberShape, validationCode, dataSource);
        break;
      case UNION:
        renderUnionShape(currentShape.asUnionShape().orElseThrow(), memberShape, validationCode, dataSource);
        break;
      case STRUCTURE:
        if (!currentShape.hasTrait(ReferenceTrait.class)) {
          final var funcCall = dataSource.concat(".Validate()");
          validationCode.append(
            CHECK_AND_RETURN_ERROR.formatted(funcCall, funcCall)
          );
        }
        break;
      default:
        break;
    }
  }

  private StringBuilder addRangeCheck(
    final MemberShape memberShape,
    final String dataSource,
    final String pointableString
  ) {
    final Shape targetShape = model.expectShape(memberShape.getTarget());
    Shape currentShape;
    StringBuilder rangeCheck = new StringBuilder();
    if (memberShape.hasTrait(RangeTrait.class)) {
      currentShape = memberShape;
    } else if (targetShape.hasTrait(RangeTrait.class)) {
      currentShape = model.expectShape(memberShape.getTarget());
    } else {
      return rangeCheck;
    }
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
    return rangeCheck;
  }

  private StringBuilder addLengthCheck(
    final MemberShape memberShape,
    final String dataSource,
    final String pointableString
  ) {
    final Shape targetShape = model.expectShape(memberShape.getTarget());
    final Shape currentShape;
    StringBuilder lengthCheck = new StringBuilder();
    if (memberShape.hasTrait(LengthTrait.class)) {
      currentShape = memberShape;
    } else if (targetShape.hasTrait(LengthTrait.class)) {
      currentShape = model.expectShape(memberShape.getTarget());
    } else {
      return lengthCheck;
    }
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
    return lengthCheck;
  }

  private StringBuilder addRequiredCheck(
    final Symbol memberSymbol,
    final MemberShape memberShape,
    final String dataSource
  ) {
    final Shape targetShape = model.expectShape(memberShape.getTarget());
    StringBuilder requiredCheck = new StringBuilder();
    if (
      !(memberShape.hasTrait(RequiredTrait.class) ||
        targetShape.hasTrait(RequiredTrait.class))
    ) {
      return requiredCheck;
    }
    if (
      GoPointableIndex.of(model).isPointable(memberShape)
    ) requiredCheck.append(
      """
      if ( %s == nil ) {
          return fmt.Errorf(\"%s is required but has a nil value.\")
      }
      """.formatted(dataSource, dataSource)
    );
    return requiredCheck;
  }

  private StringBuilder addUTFCheck(
    final MemberShape memberShape,
    final String dataSource,
    final String pointableString
  ) {
    final Shape targetShape = model.expectShape(memberShape.getTarget());
    StringBuilder UTFCheck = new StringBuilder();
    if (
      !(memberShape.hasTrait(DafnyUtf8BytesTrait.class) ||
        targetShape.hasTrait(DafnyUtf8BytesTrait.class))
    ) {
      return UTFCheck;
    }
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
    return UTFCheck;
  }

  //dataSource in non-final; Not sure if we need it as mutable.
  private void renderListShape(final ListShape currentShape, final MemberShape  memberShape, final StringBuilder validationCode, String dataSource) {
    final var itemMember = currentShape.getAllMembers().values().iterator().next();
    final var itemValidation = new StringBuilder();
    renderValidatorForEachShape(model.expectShape(itemMember.getTarget()), itemMember, false, LIST_ITEM, itemValidation);
    // If the validation function is not created and the list shape does have some constraints
    if (!validationFuncMap.containsKey(memberShape) && !itemValidation.isEmpty()) {
      final String funcName = funcNameGenerator(memberShape, "validate");
      final String funcInput = dataSource.startsWith("input") ? "" : dataSource;
      if (!funcInput.isEmpty()) {
        var inputType = GoCodegenUtils.getType(symbolProvider.toSymbol(currentShape), currentShape);
        // remove the package name because this code is generated inside smithyTypesNamespace itself
        inputType =
          inputType.replace(
            SmithyNameResolver.smithyTypesNamespace(currentShape).concat("."),
            ""
          );
        validationFuncInputTypeMap.put(memberShape, inputType);
        dataSource = "Value";
      }
      final var funcCall = "input.".concat(funcName).concat("(%s)".formatted(funcInput));
      validationCode.append(
        CHECK_AND_RETURN_ERROR.formatted(
          funcCall, funcCall
        )
      );
      validationFuncMap.put(memberShape, null);
      final var listValidation = new StringBuilder();
      listValidation.append(
        """
        for _, %s := range %s {
        """.formatted(LIST_ITEM, dataSource)
      );
      listValidation.append(itemValidation);
      listValidation.append(
        """
        }
        """
      );
      validationFuncMap.put(memberShape, listValidation.toString());
    }
  }

  private void renderMapShape(final MapShape currentShape, final MemberShape  memberShape, final StringBuilder validationCode, String dataSource) {
    final var keyMember = currentShape.getKey();
    final var valueMember = currentShape.getValue();
    final var keyValidation = new StringBuilder();
    final var valueValidation = new StringBuilder();
    renderValidatorForEachShape(model.expectShape(keyMember.getTarget()), keyMember, false, MAP_KEY, keyValidation);
    renderValidatorForEachShape(model.expectShape(valueMember.getTarget()), valueMember, false, MAP_VALUE, valueValidation);
    // Put map key or value to _ if no constraints in key or value
    final var maybeMapKey = keyValidation.isEmpty() ? "_" : MAP_KEY;
    final var maybeMapValue = valueValidation.isEmpty() ? "_" : MAP_VALUE;
    // If the validation function is not created and the map shape does have some constraints in its key and value
    if (!validationFuncMap.containsKey(memberShape) && (!keyValidation.isEmpty() || !valueValidation.isEmpty())) {
      final var funcName = funcNameGenerator(memberShape, "validate");
      final var funcInput = dataSource.startsWith("input") ? "" : dataSource;
      if (!funcInput.isEmpty()) {
        var inputType = GoCodegenUtils.getType(symbolProvider.toSymbol(currentShape), currentShape);
        // remove the package name because this code is generated inside smithyTypesNamespace itself
        inputType =
          inputType.replace(
            SmithyNameResolver.smithyTypesNamespace(currentShape).concat("."),
            ""
          );
        validationFuncInputTypeMap.put(memberShape, inputType);
        dataSource = "Value";
      }
      final var funcCall = "input.".concat(funcName).concat("(%s)".formatted(funcInput));
      validationCode.append(
        CHECK_AND_RETURN_ERROR.formatted(
          funcCall, funcCall
        )
      );
      validationFuncMap.put(memberShape, null);
      final var mapValidation = new StringBuilder();
      mapValidation.append(
        """
        for %s, %s := range %s {
        """.formatted(maybeMapKey, maybeMapValue, dataSource)
      );
      mapValidation.append(keyValidation);
      mapValidation.append(valueValidation);
      mapValidation.append(
        """
            }
        """
      );
      validationFuncMap.put(memberShape, mapValidation.toString());
    }
  }
  private void renderUnionShape(final UnionShape currentShape, final MemberShape  memberShape, final StringBuilder validationCode, String dataSource) {
  {
    final var funcName = funcNameGenerator(memberShape, "validate");
    final var funcInput = dataSource.startsWith("input") ? "" : dataSource;
    if (!funcInput.isEmpty()) {
      final var inputType = (symbolProvider.toSymbol(currentShape)).getName();

      validationFuncInputTypeMap.put(memberShape, inputType);
      dataSource = "Value";
    }
    final var funcCall = "input.".concat(funcName).concat("(%s)".formatted(funcInput));
    validationCode.append(
      CHECK_AND_RETURN_ERROR.formatted(
        funcCall, funcCall
      )
    );
    if (!validationFuncMap.containsKey(memberShape)) {
      validationFuncMap.put(memberShape, null);
      final var unionValidation = new StringBuilder();
      unionValidation.append(
        """
        switch unionType := %s.(type) {
            """.formatted(dataSource)
      );
      for (final var memberInUnion : currentShape.getAllMembers().values()) {
        unionValidation.append(
          """
          case *%s:
          """.formatted(symbolProvider.toMemberName(memberInUnion))
        );

        renderValidatorForEachShape(
          model.expectShape(memberInUnion.getTarget()),
          memberInUnion,
          false,
          "unionType.Value",
          unionValidation
        );
      }
      unionValidation.append(
        """
        // Default case should not be reached.
        default:
            panic(fmt.Sprintf("Unhandled union type: %T ", unionType))
        }
            """
      );
      validationFuncMap.put(memberShape, unionValidation.toString());
    }
  }
  }
}
