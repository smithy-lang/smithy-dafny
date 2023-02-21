using Wrappers_Compile;
using Simple.Extern;
using Simple.Extern.Wrapped;
using TypeConversion = Simple.Extern.TypeConversion ;
namespace Dafny.Simple.Extern.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleExternClient, Types._IError> WrappedSimpleExtern(Types._ISimpleExternConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N6_extern__S18_SimpleExternConfig(config);
            var impl = new SimpleExtern(wrappedConfig);
            var wrappedClient = new SimpleExternShim(impl);
            return Result<Types.ISimpleExternClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}