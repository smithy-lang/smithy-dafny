package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.smithy.codegen.core.*;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.SymbolVisitor;
import software.amazon.smithy.utils.CaseUtils;
import software.amazon.smithy.utils.StringUtils;

import java.util.Set;

public class DafnyPythonLocalServiceSymbolVisitor extends SymbolVisitor {

  public DafnyPythonLocalServiceSymbolVisitor(Model model, PythonSettings settings) {
    super(model, settings);
  }

  public String getNamespacePathForNamespace(String namespace) {
    if ("smithy.api".equals(namespace)) {
      return "smithygenerated." + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(settings.getService().getNamespace());
    }
     return "smithygenerated." + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace);
//    return namespace.equals(settings.getService().getNamespace())
//        ? SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace)
//        : "smithygenerated." + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace);
  }

  public String getDefinitionFilePathForNamespace(String namespace) {
    if ("smithy.api".equals(namespace)) {
      return SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(settings.getService().getNamespace());
    }
    System.out.println("getDefinitionFilePathForNamespace " + namespace);
     return SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace);
//    return namespace.equals(settings.getService().getNamespace())
//        ? SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace)
//        : "smithygenerated/" + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(namespace);
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
  }}

  @Override
  public Symbol structureShape(StructureShape shape) {

    String name = getDefaultShapeName(shape);
    if (shape.hasTrait(ErrorTrait.class)) {
      return createSymbolBuilder(shape, name, format("%s.errors", getNamespacePathForNamespace(shape.getId().getNamespace())))
          .definitionFile(format("%s/errors.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
          .build();
    }

    Set<ShapeId> localServiceConfigShapes = SmithyNameResolver.getLocalServiceConfigShapes(model);
    if (localServiceConfigShapes.contains(shape.getId())) {
        return createSymbolBuilder(shape, name, format("%s.config", getNamespacePathForNamespace(shape.getId().getNamespace())))
          .definitionFile(format("%s/config.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
          .build();
    }



//    else if (shape.hasTrait(PositionalTrait.class)) {
//      final MemberShape onlyMember = PositionalTrait.onlyMember(shape);
//      System.out.println("onlyMember " + onlyMember);
//      Symbol outputSymol = memberShape(onlyMember);
//      System.out.println("output " + outputSymol);
//      System.out.println("output " + outputSymol.getDefinitionFile());
//      System.out.println("output " + outputSymol.getName());
//      System.out.println("output " + outputSymol.getNamespace());
//      System.out.println("output " + outputSymol.getDeclarationFile());
//      System.out.println("output " + outputSymol.getSymbols());
////      return outputSymol;
//      final Shape targetShape = model.expectShape(onlyMember.getTarget());
//
//      if (!targetShape.getId().getNamespace().equals(settings.getService().getNamespace())) {
//        System.out.println("NOT THE SAME " + targetShape);
//        name = getDefaultShapeName(targetShape);
//        return createSymbolBuilder(targetShape, name, format("%s.models", getNamespacePathForNamespace(shape.getId().getNamespace())))
//                .definitionFile(format("%s/models.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
//                .build();
//      } else {
//        return toSymbol(targetShape);
//      }
////      name = getDefaultShapeName(targetShape);
////      return toSymbol(targetShape);
////      return createSymbolBuilder(targetShape, name, format("%s.models", getNamespacePathForNamespace(targetShape.getId().getNamespace())))
////              .definitionFile(format("%s/models.py", getDefinitionFilePathForNamespace(targetShape.getId().getNamespace())))
////              .build();
//    }
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

  @Override
  public Symbol memberShape(MemberShape shape) {
    var container = model.expectShape(shape.getContainer());
    if (container.isUnionShape()) {
      // Union members, unlike other shape members, have types generated for them.
      var containerSymbol = container.accept(this);
      var name = containerSymbol.getName() + StringUtils.capitalize(shape.getMemberName());
      return createSymbolBuilder(shape, name, format("%s.models", getNamespacePathForNamespace(shape.getId().getNamespace())))
              .definitionFile(format("./%s/models.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
              .build();
    }
    Shape targetShape = model.getShape(shape.getTarget())
            .orElseThrow(() -> new CodegenException("Shape not found: " + shape.getTarget()));
    return toSymbol(targetShape);
  }

  @Override
  public Symbol enumShape(EnumShape shape) {
    var builder = createSymbolBuilder(shape, "str");
    String name = getDefaultShapeName(shape);
    Symbol enumSymbol = createSymbolBuilder(shape, name, format("%s.models", getNamespacePathForNamespace(shape.getId().getNamespace())))
            .definitionFile(format("./%s/models.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
            .build();

    // We add this enum symbol as a property on a generic string symbol
    // rather than returning the enum symbol directly because we only
    // generate the enum constants for convenience. We actually want
    // to pass around plain strings rather than what is effectively
    // a namespace class.
    builder.putProperty("enumSymbol", escaper.escapeSymbol(shape, enumSymbol));
    return builder.build();
  }

  @Override
  public Symbol intEnumShape(IntEnumShape shape) {
    var builder = createSymbolBuilder(shape, "int");
    String name = getDefaultShapeName(shape);
    Symbol enumSymbol = createSymbolBuilder(shape, name, format("%s.models", getNamespacePathForNamespace(shape.getId().getNamespace())))
            .definitionFile(format("./%s/models.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
            .build();

    // Like string enums, int enums are plain ints when used as members.
    builder.putProperty("enumSymbol", escaper.escapeSymbol(shape, enumSymbol));
    return builder.build();
  }

  @Override
  public Symbol unionShape(UnionShape shape) {
//        System.out.println("2unionshape " + shape.getId());

    String name = getDefaultShapeName(shape);

    var unknownName = name + "Unknown";
    var unknownSymbol = createSymbolBuilder(shape, name, format("%s.models", getNamespacePathForNamespace(shape.getId().getNamespace())))
            .definitionFile(format("./%s/models.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
            .build();

    return createSymbolBuilder(shape, name, format("%s.models", getNamespacePathForNamespace(shape.getId().getNamespace())))
            .definitionFile(format("./%s/models.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
            .putProperty("fromDict", createFromDictFunctionSymbol(shape))
            .putProperty("unknown", unknownSymbol)
            .build();
  }

  @Override
  protected Symbol createAsDictFunctionSymbol(Shape shape) {
    return Symbol.builder()
            .name(String.format("_%s_as_dict", CaseUtils.toSnakeCase(shape.getId().getName())))
            .namespace(format("%s.models", getNamespacePathForNamespace(shape.getId().getNamespace())), ".")
            .definitionFile(format("./%s/models.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
            .build();
  }

  @Override
  protected Symbol createFromDictFunctionSymbol(Shape shape) {
    return Symbol.builder()
            .name(String.format("_%s_from_dict", CaseUtils.toSnakeCase(shape.getId().getName())))
            .namespace(format("%s.models", getNamespacePathForNamespace(shape.getId().getNamespace())), ".")
            .definitionFile(format("./%s/models.py", getDefinitionFilePathForNamespace(shape.getId().getNamespace())))
            .build();
  }
}
