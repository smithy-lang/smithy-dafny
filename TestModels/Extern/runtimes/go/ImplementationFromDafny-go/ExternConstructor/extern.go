package ExternConstructor

import (
	"fmt"

	"github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library/Wrappers"
	"github.com/dafny-lang/DafnyRuntimeGo/v4/dafny"
	"github.com/smithy-lang/smithy-dafny/TestModels/Extern/SimpleDafnyExternTypes"
)

type ExternConstructorClass struct {
	Value *string
}

func (e ExternConstructorClass) GetValue() Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(dafny.SeqOfChars([]dafny.Char(*e.Value)...))
}

type CompanionStruct_ExternConstructorClass_ struct {
}

var Companion_ExternConstructorClass_ = CompanionStruct_ExternConstructorClass_{}

func (CompanionStruct_ExternConstructorClass_) Build(input dafny.Sequence) Wrappers.Result {
	if input.Equals(dafny.SeqOfChars([]dafny.Char("Error")...)) {
		return Wrappers.Companion_Result_.Create_Failure_(
			SimpleDafnyExternTypes.Companion_Error_.Create_Opaque_(
				fmt.Errorf("Exception")),
		)
	}
	return Wrappers.Companion_Result_.Create_Success_(&ExternConstructorClass{func() *string {
		var s string
		for i := dafny.Iterate(input); ; {
			val, ok := i()
			if !ok {
				return &[]string{s}[0]
			} else {
				s = s + string(val.(dafny.Char))
			}
		}
	}()})
}
