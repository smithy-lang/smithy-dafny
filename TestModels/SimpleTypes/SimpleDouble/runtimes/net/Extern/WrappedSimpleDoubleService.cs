using Wrappers_Compile;
using Simple.Types.Double;
using Simple.Types.Double.Wrapped;
using TypeConversion = Simple.Types.Double.TypeConversion;
namespace Dafny.Simple.Types.Double.Wrapped
{
  public partial class __default
  {
    public static _IResult<Types.ISimpleTypesDoubleClient, Types._IError> WrappedSimpleDouble(Types._ISimpleDoubleConfig config)
    {
      var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N6_double__S18_SimpleDoubleConfig(config);
      var impl = new SimpleDouble(wrappedConfig);
      var wrappedClient = new SimpleTypesDoubleShim(impl);
      return Result<Types.ISimpleTypesDoubleClient, Types._IError>.create_Success(wrappedClient);
    }
  }
}
