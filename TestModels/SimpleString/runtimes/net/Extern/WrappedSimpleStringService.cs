using Wrappers_Compile;
using Simple.Types.String;
using Simple.Types.String.Wrapped;
using TypeConversion = Simple.Types.String.TypeConversion ;
namespace Dafny.Simple.Types.String.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleTypesStringClient, Types._IError> WrappedSimpleString(Types._ISimpleStringConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N6_string__S18_SimpleStringConfig(config);
            var impl = new SimpleString(wrappedConfig);
            var wrappedClient = new SimpleTypesStringShim(impl);
            return Result<Types.ISimpleTypesStringClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}