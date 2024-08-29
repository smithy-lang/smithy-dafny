module github.com/Smithy-dafny/TestModels/Dependencies

go 1.22.2
require github.com/dafny-lang/DafnyStandardLibGo v0.0.0
require github.com/dafny-lang/DafnyRuntimeGo v0.0.0

require github.com/Smithy-dafny/TestModels/Constraints v0.0.0
require github.com/Smithy-dafny/TestModels/Extendable v0.0.0
require github.com/Smithy-dafny/TestModels/Resource v0.0.0
require github.com/Smithy-dafny/TestModels/Errors v0.0.0

replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../DafnyRuntimeGo/
replace github.com/dafny-lang/DafnyStandardLibGo => ../../../../dafny-dependencies/StandardLibrary/runtimes/go/ImplementationFromDafny-go/

replace github.com/Smithy-dafny/TestModels/Constraints => ../../../../Constraints/runtimes/go/ImplementationFromDafny-go
replace github.com/Smithy-dafny/TestModels/Extendable => ../../../../Extendable/runtimes/go/ImplementationFromDafny-go
replace github.com/Smithy-dafny/TestModels/Resource => ../../../../Resource/runtimes/go/ImplementationFromDafny-go
replace github.com/Smithy-dafny/TestModels/Errors => ../../../../Errors/runtimes/go/ImplementationFromDafny-go