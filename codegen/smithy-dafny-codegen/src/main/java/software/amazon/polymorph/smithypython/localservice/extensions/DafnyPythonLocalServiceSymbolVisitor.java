package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.*;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.SymbolVisitor;
import software.amazon.smithy.utils.CaseUtils;
import software.amazon.smithy.utils.StringUtils;

import java.util.Set;

/**
 * Override Smithy-Python's SymbolVisitor
 * to support namespaces in other modules.
 */
public class DafnyPythonLocalServiceSymbolVisitor extends SymbolVisitor {

  public DafnyPythonLocalServiceSymbolVisitor(Model model, PythonSettings settings) {
    super(model, settings);
  }

  protected String getSymbolNamespacePathForNamespaceAndFilename(String namespace, String filename) {
    return format("%s.%s",
            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(namespace, settings),
            filename);
  }

  protected String getSymbolDefinitionFilePathForNamespaceAndFilename(String namespace, String filename) {
    String directoryFilePath;
    if ("smithy.api".equals(namespace)) {
      directoryFilePath = SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(settings.getService().getNamespace());
    } else {
      directoryFilePath = SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(namespace);
    }

    return format("./%s/%s.py",
            directoryFilePath,
            filename
            );

  }

  @Override
  public Symbol serviceShape(ServiceShape serviceShape) {
    var name = getDefaultShapeName(serviceShape);

    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      System.out.println("serviceshape is localservice " + serviceShape);
      String filename = "client";
      Symbol a= createSymbolBuilder(serviceShape, name,
              getSymbolNamespacePathForNamespaceAndFilename(serviceShape.getId().getNamespace(), filename))
              .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(serviceShape.getId().getNamespace(), filename))
              .build();
      System.out.println(a);
      return a;
    } else if (AwsSdkNameResolver.isAwsSdkShape(serviceShape)) {
      // AWS SDK: Should just be a boto3 client.
      System.out.println("serviceshape is sdk " + serviceShape);
      String filename = "shim";
//      return createStdlibSymbol(serviceShape, "Any", "typing");
      Symbol a= createSymbolBuilder(serviceShape, "Any",
              "")
              .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename("typing", filename))
              .build();
//      System.out.println(a);
      return a;
//    return a;
    } else {
      throw new IllegalArgumentException("ServiceShape not supported: " + serviceShape);
    }
  }

//  @Override
//  public Symbol serviceShape(ServiceShape serviceShape) {
//    var name = getDefaultShapeName(serviceShape);
//    String filename = "client";
//    return createStdlibSymbol(serviceShape, "Any", "typing");
////
////
////    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
////      return createStdlibSymbol(serviceShape, "Any", "typing");
//////      return createSymbolBuilder(serviceShape, name,
//////          getSymbolNamespacePathForNamespaceAndFilename(serviceShape.getId().getNamespace(), filename))
//////          .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(serviceShape.getId().getNamespace(), filename))
//////          .build();
////    } else if (AwsSdkNameResolver.isAwsSdkShape(serviceShape)) {
////      // AWS SDK: Should just be a boto3 client.
////      return createStdlibSymbol(serviceShape, "Any", "typing");
////    } else {
////      throw new IllegalArgumentException("ServiceShape not supported: " + serviceShape);
////    }
//  }

  @Override
  public Symbol resourceShape(ResourceShape resourceShape) {
    return createStdlibSymbol(resourceShape, "Any", "typing");
//    var name = getDefaultShapeName(resourceShape);
//    String filename = "references";
//
//    return createSymbolBuilder(resourceShape, name,
//            getSymbolNamespacePathForNamespaceAndFilename(resourceShape.getId().getNamespace(), filename))
//            .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(resourceShape.getId().getNamespace(), filename))
//            .build();
  }

  @Override
  public Symbol structureShape(StructureShape shape) {
    String name = getDefaultShapeName(shape);
    if (shape.hasTrait(ErrorTrait.class)) {
      String filename = "errors";
      return createSymbolBuilder(shape, name, getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
          .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
          .build();
    }

    Set<ShapeId> localServiceConfigShapes = SmithyNameResolver.getLocalServiceConfigShapes(model);
    if (localServiceConfigShapes.contains(shape.getId())) {
      String filename = "config";
        return createSymbolBuilder(shape, name, getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
          .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
          .build();
    }

    if (shape.hasTrait(ReferenceTrait.class)) {
      ShapeId referentShapeId = shape.expectTrait(ReferenceTrait.class).getReferentId();
      Shape referentShape = model.expectShape(referentShapeId);
//      if (referentShape.isResourceShape()) {
//        return resourceShape(referentShape.asResourceShape().get());
//      }
      if (referentShape.isServiceShape()) {
        System.out.println("passing structure ref into serviceshape: " + referentShape.asServiceShape().get());
        return serviceShape(referentShape.asServiceShape().get());
      } else {
//        throw new IllegalArgumentException("Referent shape is not of a supported type: " + shape);
      }
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
    String filename = "models";
    return createSymbolBuilder(shape, name, getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
        .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
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
      String filename = "models";
      return createSymbolBuilder(shape, name, getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
              .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
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
    String filename = "models";
    Symbol enumSymbol = createSymbolBuilder(shape, name, getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
            .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
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
    String filename = "models";
    Symbol enumSymbol = createSymbolBuilder(shape, name, getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
            .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
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
    String filename = "models";
    var unknownSymbol = createSymbolBuilder(shape, name, getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
            .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
            .build();

    return createSymbolBuilder(shape, name, getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
            .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
            .putProperty("fromDict", createFromDictFunctionSymbol(shape))
            .putProperty("unknown", unknownSymbol)
            .build();
  }

  @Override
  protected Symbol createAsDictFunctionSymbol(Shape shape) {
    String filename = "models";
    return Symbol.builder()
            .name(String.format("_%s_as_dict", CaseUtils.toSnakeCase(shape.getId().getName())))
            .namespace(getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename), ".")
            .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
            .build();
  }

  @Override
  protected Symbol createFromDictFunctionSymbol(Shape shape) {
    String filename = "models";
    return Symbol.builder()
            .name(String.format("_%s_from_dict", CaseUtils.toSnakeCase(shape.getId().getName())))
            .namespace(getSymbolNamespacePathForNamespaceAndFilename(shape.getId().getNamespace(), filename), ".")
            .definitionFile(getSymbolDefinitionFilePathForNamespaceAndFilename(shape.getId().getNamespace(), filename))
            .build();
  }
}
