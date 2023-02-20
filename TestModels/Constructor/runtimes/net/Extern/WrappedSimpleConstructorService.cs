using Wrappers_Compile;
using Simple.Constructor;
using Simple.Constructor.Wrapped;
using TypeConversion = Simple.Constructor.TypeConversion ;
namespace Dafny.Simple.Constructor.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleConstructorClient, Types._IError> WrappedSimpleConstructor(Types._ISimpleConstructorConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N11_constructor__S23_SimpleConstructorConfig(config);
            var impl = new SimpleConstructor(wrappedConfig);
            var wrappedClient = new SimpleConstructorShim(impl);
            return Result<Types.ISimpleConstructorClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}