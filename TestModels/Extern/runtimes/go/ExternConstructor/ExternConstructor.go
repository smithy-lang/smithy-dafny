package ExternConstructor

import (
	simpledafnyexterninternaldafnytypes "github.com/Smithy-dafny/TestModels/Extern/simpledafnyexterninternaldafnytypes"
	simpleexterntypes "github.com/Smithy-dafny/TestModels/Extern/simpleexterntypes"
	dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
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
			simpledafnyexterninternaldafnytypes.Companion_Error_.Create_Opaque_(simpleexterntypes.OpaqueError{
				"Exception"}))
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
