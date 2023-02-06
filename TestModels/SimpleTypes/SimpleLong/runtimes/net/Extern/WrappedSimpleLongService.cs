using Wrappers_Compile;
using Simple.Types.Long;
using Simple.Types.Long.Wrapped;
using TypeConversion = Simple.Types.Long.TypeConversion ;
namespace Dafny.Simple.Types.Long.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleTypesLongClient, Types._IError> WrappedSimpleLong(Types._ISimpleLongConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N4_long__S16_SimpleLongConfig(config);
            var impl = new SimpleLong(wrappedConfig);
            var wrappedClient = new SimpleTypesLongShim(impl);
            return Result<Types.ISimpleTypesLongClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}