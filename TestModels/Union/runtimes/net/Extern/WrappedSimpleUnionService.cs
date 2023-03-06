using Wrappers_Compile;
using Simple.Union;
using Simple.Union.Wrapped;
using TypeConversion = Simple.Union.TypeConversion;
namespace Dafny.Simple.Union.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleUnionClient, Types._IError> WrappedSimpleUnion(Types._ISimpleUnionConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_union__S17_SimpleUnionConfig(config);
            var impl = new SimpleUnion(wrappedConfig);
            var wrappedClient = new SimpleUnionShim(impl);
            return Result<Types.ISimpleUnionClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}