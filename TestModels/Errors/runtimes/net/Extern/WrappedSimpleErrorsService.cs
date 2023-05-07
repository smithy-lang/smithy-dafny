using Wrappers_Compile;
using Simple.Errors;
using Simple.Errors.Wrapped;
using TypeConversion = Simple.Errors.TypeConversion ;
namespace simple.errors.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<types.ISimpleErrorsClient, types._IError> WrappedSimpleErrors(types._ISimpleErrorsConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N6_errors__S18_SimpleErrorsConfig(config);
            var impl = new SimpleErrors(wrappedConfig);
            var wrappedClient = new SimpleErrorsShim(impl);
            return Result<types.ISimpleErrorsClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
