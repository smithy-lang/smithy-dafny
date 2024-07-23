// Interface ISimpleConstraintsClient
// Dafny trait ISimpleConstraintsClient compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public interface ISimpleConstraintsClient {
  public Wrappers_Compile.Result<GetConstraintsOutput, Error> GetConstraints(GetConstraintsInput input);
}
