using Wrappers_Compile;
using Simple.Constraints;
using Simple.Constraints.Wrapped;
using TypeConversion = Simple.Constraints.TypeConversion ;
namespace simple.constraints.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleConstraintsClient, Types._IError> WrappedSimpleConstraints(Types._ISimpleConstraintsConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N11_constraints__S23_SimpleConstraintsConfig(config);
            var impl = new SimpleConstraints(wrappedConfig);
            var wrappedClient = new SimpleConstraintsShim(impl);
            return Result<Types.ISimpleConstraintsClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}
