module github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/test

go 1.22.2

require github.com/dafny-lang/DafnyStandardLibGo v0.0.0

require github.com/dafny-lang/DafnyRuntimeGo v0.0.0

require github.com/smithy-lang/smithy-dafny/TestModels/Aggregate v0.0.0

replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../DafnyRuntimeGo/

replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

replace github.com/smithy-lang/smithy-dafny/TestModels/Aggregate => ../ImplementationFromDafny-go