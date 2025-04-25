package software.amazon.polymorph.traits;

import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.neighbor.Walker;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.validation.AbstractValidator;
import software.amazon.smithy.model.validation.ValidationEvent;

public class UnsupportedFeaturesValidator extends AbstractValidator {

  private static final Set<ShapeType> COMMON_SUPPORTED_SHAPE_TYPES = EnumSet.of(
    ShapeType.BOOLEAN,
    ShapeType.BLOB,
    ShapeType.DOUBLE,
    ShapeType.ENUM,
    ShapeType.INTEGER,
    ShapeType.LIST,
    ShapeType.LONG,
    ShapeType.MAP,
    ShapeType.MEMBER,
    ShapeType.OPERATION,
    ShapeType.STRING,
    ShapeType.SERVICE,
    ShapeType.STRUCTURE,
    ShapeType.TIMESTAMP,
    ShapeType.UNION
  );

  private static final Set<ShapeType> SUPPORTED_SHAPES_LOCAL_SERVICE = Stream
    .concat(
      COMMON_SUPPORTED_SHAPE_TYPES.stream(),
      Stream.of(
        // Playing it safe and not claiming to support this in SDK style mode yet,
        // since we might be generating code that only makes sense for local services.
        ShapeType.RESOURCE
      )
    )
    .collect(Collectors.toSet());

  private static final List<ShapeId> COMMON_SUPPORTED_TRAITS = List
    .of(
      "smithy.api#box",
      "smithy.api#documentation",
      "smithy.api#error",
      "smithy.api#enum",
      "smithy.api#enumValue",
      "smithy.api#input",
      "smithy.api#length",
      "smithy.api#output",
      "smithy.api#required",
      "smithy.api#range",
      "smithy.api#readonly",
      "smithy.synthetic#enum"
    )
    .stream()
    .map(ShapeId::from)
    .toList();

  private static final Set<ShapeId> SUPPORTED_TRAITS_LOCAL_SERVICE = Stream
    .concat(
      COMMON_SUPPORTED_TRAITS.stream(),
      Stream
        .of(
          // This is not actually true at all,
          // but Smithy liberally injects @default into Smithy 1.0 models
          // to make implicit semantics explicit.
          // Rather than require a ton of suppressions and risk alarm fatigue,
          // this is tracked as a soundness bug instead:
          // https://github.com/smithy-lang/smithy-dafny/issues/544
          "smithy.api#default",
          // For those that literally can't be used for non-local services,
          // we probably want model validation to forbid them instead,
          "aws.polymorph#extendable",
          "aws.polymorph#localService",
          "aws.polymorph#dafnyUtf8Bytes",
          "aws.polymorph#javadoc",
          "aws.polymorph#positional",
          "aws.polymorph#reference",
          // Not technically supported for all target languages yet.
          // But we also emit a separate WARNING for this in NoReferencesInSmokeTestsValidator anyway.
          "smithy.test#smokeTests"
        )
        .map(ShapeId::from)
    )
    .collect(Collectors.toSet());

  private static final Set<ShapeId> SUPPORTED_TRAITS_AWS_SERVICE = Stream
    .concat(
      COMMON_SUPPORTED_TRAITS.stream(),
      Stream
        .of(
          // Most of these are protocol details handled by the wrapped SDKs
          // and not relevant for SDK consumers,
          // so it is valid and safe for our codegen to intentionally ignore them.
          "aws.api#clientEndpointDiscovery",
          "aws.api#clientDiscoveredEndpoint",
          "aws.api#service",
          "aws.auth#sigv4",
          "aws.protocols#awsJson1_0",
          "aws.protocols#awsJson1_1",
          "aws.protocols#awsQuery",
          "aws.protocols#awsQueryError",
          "aws.protocols#httpChecksum",
          "smithy.api#httpPayload",
          "aws.protocols#restJson1",
          "aws.protocols#restXml",
          "smithy.api#default",
          "smithy.api#deprecated",
          "smithy.api#endpoint",
          // This is safe since the enum value is only relevant on the wire
          "smithy.api#enumValue",
          // We don't generate examples yet, but that's harmless
          "smithy.api#examples",
          "smithy.api#http",
          "smithy.api#httpError",
          "smithy.api#httpHeader",
          "smithy.api#httpLabel",
          "smithy.api#httpPrefixHeaders",
          "smithy.api#httpQuery",
          "smithy.api#idempotencyToken",
          "smithy.api#paginated",
          "smithy.api#pattern",
          "smithy.api#sensitive",
          "smithy.api#suppress",
          "smithy.api#retryable",
          "smithy.api#timestampFormat",
          "smithy.api#title",
          "smithy.api#uniqueItems",
          "smithy.api#xmlFlattened",
          "smithy.api#xmlName",
          "smithy.api#xmlNamespace",
          "smithy.rules#clientContextParams",
          "smithy.rules#contextParam",
          "smithy.rules#endpointTests",
          "smithy.rules#endpointRuleSet",
          // We don't really support this yet, since it implies extra API
          // methods we don't generate, but at least we don't generate incorrect code.
          "smithy.waiters#waitable"
        )
        .map(ShapeId::from)
    )
    .collect(Collectors.toSet());

  @Override
  public List<ValidationEvent> validate(Model model) {
    List<ValidationEvent> events = new ArrayList<>();

    for (ServiceShape serviceShape : model.getServiceShapes()) {
      if (serviceShape.hasTrait(ServiceTrait.class)) {
        checkForUnsupportedFeatures(
          model,
          serviceShape,
          events,
          "AWS",
          COMMON_SUPPORTED_SHAPE_TYPES,
          SUPPORTED_TRAITS_AWS_SERVICE
        );
      }
      if (serviceShape.hasTrait(LocalServiceTrait.class)) {
        checkForUnsupportedFeatures(
          model,
          serviceShape,
          events,
          "local",
          SUPPORTED_SHAPES_LOCAL_SERVICE,
          SUPPORTED_TRAITS_LOCAL_SERVICE
        );
      }
    }

    return events;
  }

  private void checkForUnsupportedFeatures(
    Model model,
    ServiceShape service,
    List<ValidationEvent> events,
    String serviceKindLabel,
    Collection<ShapeType> supportedShapes,
    Collection<ShapeId> supportedTraits
  ) {
    for (Shape shape : new Walker(model).walkShapes(service)) {
      if (!supportedShapes.contains(shape.getType())) {
        // This is an ERROR event rather than DANGER for two reasons:
        // 1. It's very unlikely codegen will somehow be correct for an unsupported shape type if this is just suppressed.
        // 2. Smithy itself eats events other than ERRORs on prelude shapes, under the assumption
        //    that issues with the prelude should not be the user's concern.
        // We could address 2. by putting the event on the reference to the prelude shape instead,
        // but given 1. it doesn't seem worth it.
        events.add(
          error(
            shape,
            "smithy-dafny does not support this shape type for %s services: %s.".formatted(
                serviceKindLabel,
                shape.getType()
              )
          )
        );
      }

      for (ShapeId traitId : shape.getAllTraits().keySet()) {
        if (
          !supportedTraits.contains(traitId) &&
          ModelUtils.isInServiceNamespace(shape, service)
        ) {
          events.add(
            danger(
              shape,
              "smithy-dafny does not support this trait for %s services: %s.".formatted(
                  serviceKindLabel,
                  traitId
                )
            )
          );
        }
      }
    }
  }
}
