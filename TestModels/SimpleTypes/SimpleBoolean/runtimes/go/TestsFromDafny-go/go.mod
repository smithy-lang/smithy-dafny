module github.com/smithy-lang/smithy-dafny/TestModels/SimpleTypes/SimpleBoolean/test

go 1.23.0

require github.com/dafny-lang/DafnyStandardLibGo v0.0.0

require (
	github.com/dafny-lang/DafnyRuntimeGo v0.0.0
	github.com/smithy-lang/smithy-dafny/TestModels/SimpleTypes/SimpleBoolean v0.0.0
)

replace github.com/smithy-lang/smithy-dafny/TestModels/SimpleTypes/SimpleBoolean v0.0.0 => ../ImplementationFromDafny-go

//TODO: Drop this after Dafny fixes the https://t.corp.amazon.com/P150784381
replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../../DafnyRuntimeGo/

replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/
