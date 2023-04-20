// Interface ISimpleDependenciesClient
// Dafny trait ISimpleDependenciesClient compiled into Java
package Dafny.Simple.Dependencies.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public interface ISimpleDependenciesClient {
  public Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Error> GetSimpleResource(Dafny.Simple.Resources.Types.GetResourcesInput input);
  public Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Error> UseSimpleResource(UseSimpleResourceInput input);
  public Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Error> UseLocalConstraintsService(Dafny.Simple.Constraints.Types.GetConstraintsInput input);
  public Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Error> UseLocalExtendableResource(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataInput input);
  public Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Error> LocalExtendableResourceAlwaysModeledError(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput input);
  public Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Error> LocalExtendableResourceAlwaysMultipleErrors(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput input);
  public Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Error> LocalExtendableResourceAlwaysNativeError(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput input);
}
