using Wrappers_Compile;
using Simple.Refinement;
using Simple.Refinement.Wrapped;
using TypeConversion = Simple.Refinement.TypeConversion;
namespace Dafny.Simple.Refinement.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleRefinementClient, Types._IError> WrappedSimpleRefinement(Types._ISimpleRefinementConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N10_refinement__S22_SimpleRefinementConfig(config);
            var impl = new SimpleRefinement(wrappedConfig);
            var wrappedClient = new SimpleRefinementShim(impl);
            return Result<Types.ISimpleRefinementClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}