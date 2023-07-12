package software.amazon.polymorph.smithypython.nameresolver;

import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.ServiceShape;

public class PythonNameResolver {

  // TODO: Refactor into nameresovler
  public static String clientForService(ServiceShape serviceShape) {
      if (serviceShape.hasTrait(LocalServiceTrait.class)) {
          return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Client";
      } else {
          throw new UnsupportedOperationException("Non-local services not supported");
      }
  }

  // TODO: Refactor into nameresovler
  public static String shimForService(ServiceShape serviceShape) {
      if (serviceShape.hasTrait(LocalServiceTrait.class)) {
          return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Shim";
      } else {
          throw new UnsupportedOperationException("Non-local services not supported");
      }
  }
}
