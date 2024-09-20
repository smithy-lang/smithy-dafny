module github.com/dafny-lang/DafnyStandardLibGo

go 1.23.0

//TODO: Drop this after Dafny fixes the https://t.corp.amazon.com/P150784381
replace github.com/dafny-lang/DafnyRuntimeGo => ../../../../../../DafnyRuntimeGo/

require github.com/dafny-lang/DafnyRuntimeGo v0.0.0-00010101000000-000000000000
