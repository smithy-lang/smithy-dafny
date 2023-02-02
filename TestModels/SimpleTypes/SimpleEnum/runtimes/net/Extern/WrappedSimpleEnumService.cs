using Wrappers_Compile;
using Simple.Types.Enum;
using Simple.Types.Enum.Wrapped;
using TypeConversion = Simple.Types.Enum.TypeConversion ;
namespace Dafny.Simple.Types.Enum.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleTypesEnumClient, Types._IError> WrappedSimpleEnum(Types._ISimpleEnumConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N4_enum__S16_SimpleEnumConfig(config);
            var impl = new SimpleEnum(wrappedConfig);
            var wrappedClient = new SimpleTypesEnumShim(impl);
            return Result<Types.ISimpleTypesEnumClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}