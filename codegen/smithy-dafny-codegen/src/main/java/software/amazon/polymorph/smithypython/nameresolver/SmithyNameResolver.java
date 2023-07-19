package software.amazon.polymorph.smithypython.nameresolver;

import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.ServiceShape;

/**
 * Contains utility functions that map Smithy shapes
 * to useful strings used in Smithy-Python generated code.
 */
public class SmithyNameResolver {

  public static String clientForService(ServiceShape serviceShape) {
      if (serviceShape.hasTrait(LocalServiceTrait.class)) {
          return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Client";
      } else {
          throw new UnsupportedOperationException("Non-local services not supported");
      }
  }

  public static String shimForService(ServiceShape serviceShape) {
      if (serviceShape.hasTrait(LocalServiceTrait.class)) {
          return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Shim";
      } else {
          throw new UnsupportedOperationException("Non-local services not supported");
      }
  }
}
