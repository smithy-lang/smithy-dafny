package software.amazon.polymorph.smithyjava;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.TypeName;

import java.util.List;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;

import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;

// TODO: We can shrink our code base by combining
//  BuilderMemberSpec w/ PolymorphFieldSpec.
// They serve very similar purposes:
// Parsing Traits from Smithy Shapes for Builder Class generators.
public class BuilderMemberSpec {
    public final static List<BuilderMemberSpec> THROWABLE_ARGS = List.of(
            new BuilderMemberSpec(TypeName.get(String.class), "message"),
            new BuilderMemberSpec(TypeName.get(Throwable.class), "cause")
    );

    public final static List<BuilderMemberSpec> OPAQUE_ARGS = List.of(
            new BuilderMemberSpec(TypeName.get(Object.class), "obj")
    );

    @Nonnull public final TypeName type;
    @Nonnull public final String name;
    @Nullable public final TypeName interfaceType;
    @Nullable public final CodeBlock wrapCall;

    public BuilderMemberSpec(MemberShape memberShape, JavaLibrary subject) {
        ModelUtils.ResolvedShapeId resolvedShapeId = ModelUtils.resolveShape(memberShape.getTarget(), subject.model);
        Shape resolvedShape = subject.model.expectShape(resolvedShapeId.resolvedId());
        this.type = subject.nativeNameResolver.typeForShape(resolvedShapeId.naiveId());
        this.name = memberShape.getMemberName();
        if (
                (resolvedShape.isServiceShape() || resolvedShape.isResourceShape())
                && !AwsSdkNameResolverHelpers.isInAwsSdkNamespace(resolvedShapeId.resolvedId())
        ) {
            // If target is a non-AWS Service/Resource,
            // the output type should be an interface OR LocalService
            this.interfaceType = Native.classNameForInterfaceOrLocalService(
                    resolvedShape, subject.sdkVersion);
            // And we will need to wrap it
            this.wrapCall = subject.wrapWithShim(resolvedShapeId.resolvedId(),
                    CodeBlock.of(this.name));
        } else {
            this.interfaceType = null;
            this.wrapCall = null;
        }
    }

    private BuilderMemberSpec(@Nonnull TypeName type, @Nonnull String name) {
        this.interfaceType = null;
        this.wrapCall = null;
        this.name = name;
        this.type = type;
    }

    public static List<BuilderMemberSpec> collectionOfErrorsBuilderMemberSpecs(String packageName) {
        TypeName type = CollectionOfErrors.getArg(packageName);
        String name = "list";
        return List.of(new BuilderMemberSpec(type, name));
    }

    public static BuilderMemberSpec serviceShimMemberSpec(
            LocalServiceTrait trait, JavaLibrary subject)
    {
        TypeName type = subject.nativeNameResolver.typeForShape(trait.getConfigId());
        String name = trait.getConfigId().getName();
        return new BuilderMemberSpec(type, name);
    }
}
