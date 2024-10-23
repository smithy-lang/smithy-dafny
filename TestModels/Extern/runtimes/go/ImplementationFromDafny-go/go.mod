module github.com/smithy-lang/smithy-dafny/TestModels/Extern

go 1.23.0

require (
	github.com/dafny-lang/DafnyRuntimeGo/v4 v4.8.0
	github.com/dafny-lang/DafnyStandardLibGo v0.0.0
)

replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/
