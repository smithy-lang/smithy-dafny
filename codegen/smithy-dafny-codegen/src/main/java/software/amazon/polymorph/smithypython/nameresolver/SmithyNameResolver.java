package software.amazon.polymorph.smithypython.nameresolver;

import java.util.Locale;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;

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

  public static String getPythonModuleNamespaceForSmithyNamespace(String smithyNamespace) {
    return smithyNamespace.toLowerCase(Locale.ROOT).replace(".", "_");
  }

  public static String getSmithyGeneratedModuleNamespaceForSmithyNamespace(String smithyNamespace,
      GenerationContext codegenContext) {

    System.out.println("getSmithyGeneratedModuleNamespaceForSmithyNamespace");
    System.out.println(getPythonModuleNamespaceForSmithyNamespace(smithyNamespace));
    System.out.println(smithyNamespace);


    return
        getPythonModuleNamespaceForSmithyNamespace(smithyNamespace).contains(codegenContext.settings().getModuleName())
        ? ""
        :  getPythonModuleNamespaceForSmithyNamespace(smithyNamespace) + ".smithygenerated";
  }
}
