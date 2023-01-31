using Wrappers_Compile;
using Simple.Types.Boolean;
using Simple.Types.Boolean.Wrapped;
using TypeConversion = Simple.Types.Boolean.TypeConversion ;
namespace Dafny.Simple.Types.Boolean.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleTypesBooleanClient, Types._IError> WrappedSimpleBoolean(Types._ISimpleBooleanConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N7_boolean__S19_SimpleBooleanConfig(config);
            var impl = new SimpleBoolean(wrappedConfig);
            var wrappedClient = new SimpleTypesBooleanShim(impl);
            return Result<Types.ISimpleTypesBooleanClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}