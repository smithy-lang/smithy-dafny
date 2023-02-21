using Wrappers_Compile;
using Simple.Extern;
using TypeConversion = Simple.Extern.TypeConversion ;
using System.IO;
using System.Text;
namespace SimpleExternImpl_Compile
{
    public partial class __default {
        public static Wrappers_Compile._IResult<Dafny.Simple.Extern.Types._IGetExternOutput, Dafny.Simple.Extern.Types._IError> GetExtern(SimpleExternImpl_Compile._IConfig config, Dafny.Simple.Extern.Types._IGetExternInput input) {
            // var blobValue = TypeConversion.ToDafny_N6_simple__N6_extern__S15_GetExternOutput__M9_blobValue(new MemoryStream(Encoding.Unicode.GetBytes("TestBlobValue")));
            // var booleanValue = TypeConversion.ToDafny_N6_simple__N6_extern__S15_GetExternOutput__M12_booleanValue(false);
            // var stringValue = TypeConversion.ToDafny_N6_simple__N6_extern__S15_GetExternOutput__M11_stringValue("TestString");
            // var integerValue = TypeConversion.ToDafny_N6_simple__N6_extern__S15_GetExternOutput__M12_integerValue(0);
            // var longValue = TypeConversion.ToDafny_N6_simple__N6_extern__S15_GetExternOutput__M9_longValue(0);
            var output = new Dafny.Simple.Extern.Types.GetExternOutput(input.dtor_blobValue, input.dtor_booleanValue, input.dtor_stringValue, input.dtor_integerValue, input.dtor_longValue);
            return Result<Dafny.Simple.Extern.Types._IGetExternOutput, Dafny.Simple.Extern.Types._IError>.create_Success(output);
        }
    }
}