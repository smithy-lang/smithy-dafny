using Wrappers_Compile;
using TypeConversion = Example.Simpletypes.TypeConversion;
using SimpleTypes = Example.Simpletypes.SimpleTypes;
using SimpleTypesServiceShim = Example.Simpletypes.Wrapped.SimpleTypesServiceShim;
namespace Dafny.Example.Simpletypes.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleTypesServiceClient, Types._IError> WrappedSimpleTypes(Types._IEmptyConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N7_example__N11_simpletypes__S11_EmptyConfig(config);
            var impl = new SimpleTypes(wrappedConfig);
            var wrappedClient = new SimpleTypesServiceShim(impl);
            return Result<Types.ISimpleTypesServiceClient, Types._IError>.create_Failure(Types.Error.create_Opaque("d"));
        }
    }
}