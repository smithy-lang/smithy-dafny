using Wrappers_Compile;
using Simple.Extern;
using TypeConversion = Simple.Extern.TypeConversion ;
using System.IO;
using System.Text;
namespace SimpleExternImpl_Compile
{
    public partial class __default {
        public static Wrappers_Compile._IResult<Dafny.Simple.Extern.Types._IGetExternOutput, Dafny.Simple.Extern.Types._IError> GetExtern(SimpleExternImpl_Compile._IConfig config, Dafny.Simple.Extern.Types._IGetExternInput input) {
            var output = new Dafny.Simple.Extern.Types.GetExternOutput(input.dtor_blobValue, input.dtor_booleanValue, input.dtor_stringValue, input.dtor_integerValue, input.dtor_longValue);
            return Result<Dafny.Simple.Extern.Types._IGetExternOutput, Dafny.Simple.Extern.Types._IError>.create_Success(output);
        }

        public static Wrappers_Compile._IResult<Dafny.Simple.Extern.Types._IExternMustErrorOutput, Dafny.Simple.Extern.Types._IError> ExternMustError(SimpleExternImpl_Compile._IConfig config, Dafny.Simple.Extern.Types._IExternMustErrorInput input) {
            return Result<Dafny.Simple.Extern.Types._IExternMustErrorOutput, Dafny.Simple.Extern.Types._IError>.create_Failure(Dafny.Simple.Extern.Types.Error.create_Opaque(new System.Exception("MustError")));
        }
    }
}

namespace ExternConstructor {
    public class ExternConstructorClass {
        public ExternConstructorClass() {
            // C# constructor can throw error. In these cases, dafny would halt the whole program
            // (since constructor can't have a return type and can't return the error to dafny).
            // throw new System.Exception("ConstructorFailed"));
        }
    }
}