package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.codegen.core.ReservedWordSymbolProvider;
import software.amazon.smithy.codegen.core.ReservedWords;
import software.amazon.smithy.codegen.core.ReservedWordsBuilder;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.SymbolVisitor;
import software.amazon.smithy.utils.StringUtils;

public class DafnyPythonLocalServiceSymbolVisitor extends SymbolVisitor {

  public DafnyPythonLocalServiceSymbolVisitor(Model model, PythonSettings settings) {
    super(model, settings);
  }

  private String getNamespacePathForNamespace(String namespace) {
    if ("smithy.api".equals(namespace)) {
      return SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(settings.getService().getNamespace());
    }
    return namespace.equals(settings.getService().getNamespace())
        ? SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace)
        : SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace) + ".smithygenerated";
  }

  private String getDefinitionFilePathForNamespace(String namespace) {
    if ("smithy.api".equals(namespace)) {
      return SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(settings.getService().getNamespace());
    }
    return namespace.equals(settings.getService().getNamespace())
        ? SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace)
        : SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace) + "/smithygenerated";
  }

  @Override
  public Symbol serviceShape(ServiceShape serviceShape) {
    var name = getDefaultShapeName(serviceShape);



    if (serviceShape.getId().equals(settings.getService())) {
      return createSymbolBuilder(serviceShape, name,
          format("%s.client", getNamespacePathForNamespace(serviceShape.getId().getNamespace())))
          .definitionFile(format("%s/client.py",
              getDefinitionFilePathForNamespace(serviceShape.getId().getNamespace())))
          .build();
    } else {
      // AWS SDK: Should just be a boto3 client. TODO-Python: Type this
      return createStdlibSymbol(serviceShape, "Any", "typing");
//    }
  }}

  @Override
  public Symbol structureShape(StructureShape shape) {

    String name = getDefaultShapeName(shape);
    if (shape.hasTrait(ErrorTrait.class)) {
      return createSymbolBuilder(shape, name, format("%s.errors", getNamespacePathForNamespace(shape.getId().getNamespace())))
          .definitionFile(format("%s/errors.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
          .build();
    }
    return createSymbolBuilder(shape, name, format("%s.models", getNamespacePathForNamespace(shape.getId().getNamespace())))
        .definitionFile(format("%s/models.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
        .build();
  }

  @Override
  protected boolean targetRequiresDictHelpers(Shape target) {
    if (!target.getId().getNamespace().equals(service.getId().getNamespace())) {
      return false;
    } else {
      return super.targetRequiresDictHelpers(target);
    }
  }
}
