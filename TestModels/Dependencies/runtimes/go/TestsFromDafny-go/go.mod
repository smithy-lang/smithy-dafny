module github.com/smithy-lang/smithy-dafny/TestModels/Dependencies/test

go 1.23.0

require github.com/dafny-lang/DafnyStandardLibGo v0.0.0

require github.com/dafny-lang/DafnyRuntimeGo v0.0.0

require github.com/smithy-lang/smithy-dafny/TestModels/Constraints v0.0.0

require github.com/smithy-lang/smithy-dafny/TestModels/Extendable v0.0.0

require github.com/smithy-lang/smithy-dafny/TestModels/Resource v0.0.0

require (
	github.com/smithy-lang/smithy-dafny/TestModels/Dependencies v0.0.0
	github.com/smithy-lang/smithy-dafny/TestModels/Errors v0.0.0 // indirect
)

replace github.com/smithy-lang/smithy-dafny/TestModels/Dependencies v0.0.0 => ../ImplementationFromDafny-go

//TODO: Drop this after Dafny fixes the https://t.corp.amazon.com/P150784381
replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../DafnyRuntimeGo/

replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

replace github.com/smithy-lang/smithy-dafny/TestModels/Constraints v0.0.0 => ../../../../Constraints/runtimes/go/ImplementationFromDafny-go

replace github.com/smithy-lang/smithy-dafny/TestModels/Extendable v0.0.0 => ../../../../Extendable/runtimes/go/ImplementationFromDafny-go

replace github.com/smithy-lang/smithy-dafny/TestModels/Resource v0.0.0 => ../../../../Resource/runtimes/go/ImplementationFromDafny-go

replace github.com/smithy-lang/smithy-dafny/TestModels/Errors v0.0.0 => ../../../../Errors/runtimes/go/ImplementationFromDafny-go
