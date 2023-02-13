using Wrappers_Compile;
using Simple.Errors;
using Simple.Errors.Wrapped;
using TypeConversion = Simple.Errors.TypeConversion ;
namespace Dafny.Simple.Errors.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleErrorsClient, Types._IError> WrappedSimpleErrors(Types._ISimpleErrorsConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N6_errors__S18_SimpleErrorsConfig(config);
            var impl = new SimpleErrors(wrappedConfig);
            var wrappedClient = new SimpleErrorsShim(impl);
            return Result<Types.ISimpleErrorsClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}