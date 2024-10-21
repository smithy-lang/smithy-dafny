module github.com/smithy-lang/smithy-dafny/TestModels/SimpleTypes/SimpleDouble/test

go 1.23.0

replace github.com/smithy-lang/smithy-dafny/TestModels/SimpleTypes/SimpleDouble v0.0.0 => ../ImplementationFromDafny-go

//TODO: Drop this after Dafny fixes the https://t.corp.amazon.com/P150784381
replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../../DafnyRuntimeGo/

replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

require (
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.8.0
	github.com/dafny-lang/DafnyStandardLibGo v0.0.0
	github.com/smithy-lang/smithy-dafny/TestModels/SimpleTypes/SimpleDouble v0.0.0
)
