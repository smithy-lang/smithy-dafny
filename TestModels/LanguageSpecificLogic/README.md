# SimpleExternV2

This project tests implementing a [dafny extern](https://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf#15) using the "V2 Extern" system.
This models and its shapes are based on to operations in the `Extern` TestModel.

The differences between these two TestModels are:
* V2 suffixes are appended to classes and operations
* The NET implementation of the `simple.dafnyexternv2.internaldafny` extern contains an extern method that is not present in other languages (as a demonstration; see below)
* The `ExternV2Constructor` is moved to `simple.dafnyexternv2.internaldafny.ExternV2Constructor` 

This TestModel also demonstrates a "V2" extern system.

The "V1" extern system applies an `{:extern "..."}` attribute to a module to signal an extern.
This worked for .NET and Java, where this extern string was valid in both languages.
However, this does not work for Python and Go, where this string is not applicable.

The "V2" extern system is intended to allow per-language extern strings.
This system uses the `replaceable` and `replaces` keywords
in conjunction with the `outer-module` compile flag
to allow a module to have idiomatic extern names in each target language.

Under this V2 system, a Dafny developer should not directly mark a module as `extern` if the path to the extern module depends on language-specific features.
(e.g. an `{:extern "sample.namespace.MyExternModule"}` makes sense for Java externs, but the `.`s will break Python externs.)

Instead of marking this module as `extern`, the developer should mark the module as `replaceable`.
Then, they should create a new module that `replaces` the `replaceable` module.
The developer should add the `extern` attribute to this new module.
This module's `extern` attribute will define a namespace-path-syntax-specific extern name (e.g. `.`s vs `_`s).
For each path syntax, the developer should create a separate module that `replaces` the `replaceable` module.

This TestModel demonstrates per-path-syntax externs in the `ExternV2Constructor` module and in the `WrappedTestDotNamespaced` module.

A second benefit of the V2 extern system is allowing Dafny to generate code only for particular languages.
If an extern module requires specific behavior in a particular language, the extern should NOT be replaced in the path-syntax specific module.
Instead, the developer should write a new file per-language that:
1. `include`s the path-syntax specific module. (This includes any shared extern definitions in the target language.)
2. `replaces` the `replaceable` extern module. Here, the developer can add Dafny code specific to the language under generation.

This TestModel demonstrates per-langauge externs in the `SimpleExternV2` module.

(TODO: Implement outer-module or similar mechanism: https://sim.amazon.com/issues/CrypTool-5260)

## Build
### .NET
1. Generate the Wrappers using `polymorph`
```
make polymorph_dafny polymorph_net
```

2. Transpile the tests (and implementation) to the target runtime.
```
make transpile_net
```

3. Generate the executable in the .NET and execute the tests
```
make test_net
```

## Development
1. To add another target runtime support, edit the `Makefile` and add the appropriate recipe to generate the `polymorph` wrappers, and dafny transpilation.
2. Provide any glue code between dafny and target runtime if required.
3. Build, execute, and test in the target runtime.

*Example*

`--output-dotnet <PATH>` in the `gradlew run` is used to generate the polymorph wrappers. Similarly `--compileTarget:<RUNTIME>` flags is used in dafny recipe to transpile to C#.
