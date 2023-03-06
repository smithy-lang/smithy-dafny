using Wrappers_Compile;
using Simple.Dependencies;
using Simple.Dependencies.Wrapped;
using TypeConversion = Simple.Dependencies.TypeConversion ;
namespace Dafny.Simple.Dependencies.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleDependenciesClient, Types._IError> WrappedSimpleDependencies(Types._ISimpleDependenciesConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N12_dependencies__S24_SimpleDependenciesConfig(config);
            var impl = new SimpleDependencies(wrappedConfig);
            var wrappedClient = new SimpleDependenciesShim(impl);
            return Result<Types.ISimpleDependenciesClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}