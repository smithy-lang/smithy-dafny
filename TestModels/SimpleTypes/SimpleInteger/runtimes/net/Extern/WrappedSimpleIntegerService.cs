using Wrappers_Compile;
using Simple.Types.Integer;
using Simple.Types.Integer.Wrapped;
using TypeConversion = Simple.Types.Integer.TypeConversion ;
namespace Dafny.Simple.Types.Integer.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleTypesIntegerClient, Types._IError> WrappedSimpleInteger(Types._ISimpleIntegerConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N7_integer__S19_SimpleIntegerConfig(config);
            var impl = new SimpleInteger(wrappedConfig);
            var wrappedClient = new SimpleTypesIntegerShim(impl);
            return Result<Types.ISimpleTypesIntegerClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}