package SimpleExternImpl

import (
	"github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library/Wrappers"
	"github.com/smithy-lang/smithy-dafny/TestModels/Extern/SimpleDafnyExternTypes"
)

func (CompanionStruct_Default___) GetExtern(c Config, input SimpleDafnyExternTypes.GetExternInput) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(SimpleDafnyExternTypes.Companion_GetExternOutput_.Create_GetExternOutput_(input.Dtor_blobValue(),
		input.Dtor_booleanValue(),
		input.Dtor_stringValue(),
		input.Dtor_integerValue(),
		input.Dtor_longValue()))

}
func (CompanionStruct_Default___) ExternMustError(c Config, input SimpleDafnyExternTypes.ExternMustErrorInput) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Failure_(
		SimpleDafnyExternTypes.Companion_Error_.Create_Opaque_(
			input.Dtor_value()))
}
