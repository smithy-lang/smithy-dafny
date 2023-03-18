// Interface ISimpleConstraintsClient
// Dafny trait ISimpleConstraintsClient compiled into Java
package Dafny.Simple.Constraints.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public interface ISimpleConstraintsClient {
  public Wrappers_Compile.Result<GetConstraintsOutput, Error> GetConstraints(GetConstraintsInput input);
}
