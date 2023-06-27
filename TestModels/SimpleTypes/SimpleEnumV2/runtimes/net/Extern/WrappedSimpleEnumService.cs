using Wrappers_Compile;
using Simple.Types.EnumV2;
using Simple.Types.EnumV2.Wrapped;
using TypeConversion = Simple.Types.EnumV2.TypeConversion ;
namespace Dafny.Simple.Types.EnumV2.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleTypesEnumV2Client, Types._IError> WrappedSimpleEnumV2(Types._ISimpleEnumV2Config config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N6_enumV2__S18_SimpleEnumV2Config(config);
            var impl = new SimpleEnumV2(wrappedConfig);
            var wrappedClient = new SimpleTypesEnumV2Shim(impl);
            return Result<Types.ISimpleTypesEnumV2Client, Types._IError>.create_Success(wrappedClient);
        }
    }
}
