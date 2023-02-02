using Wrappers_Compile;
using Simple.Types.Blob;
using Simple.Types.Blob.Wrapped;
using TypeConversion = Simple.Types.Blob.TypeConversion ;
namespace Dafny.Simple.Types.Blob.Wrapped
{
    public partial class __default {
        public static _IResult<Types.ISimpleTypesBlobClient, Types._IError> WrappedSimpleBlob(Types._ISimpleBlobConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N4_blob__S16_SimpleBlobConfig(config);
            var impl = new SimpleBlob(wrappedConfig);
            var wrappedClient = new SimpleTypesBlobShim(impl);
            return Result<Types.ISimpleTypesBlobClient, Types._IError>.create_Success(wrappedClient);
        }
    }
}