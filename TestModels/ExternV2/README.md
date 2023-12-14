# SimpleExternV2

This project tests implementing a [dafny extern](https://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf#15) using the "V2 Extern" system.
This models and its shapes are based on to operations in the `Extern` TestModel. The differences are:
* V2 suffixes are appended to classes and operations
* The NET implementation of the extern "simple.dafnyexternv2.internaldafny"

This V2 extern system uses the `replaceable` and `replaces` keywords in conjunction with the `outer-module` compile flag to allow a module to have idiomatic extern names in each target language.

Under this V2 system, a Dafny developer should not mark a module as `extern` if the path to the extern module depends on language-specific features. (e.g. an `:extern "sample.namespace.MyExternModule"` makes sense for Java externs, but the `.`s will break Python externs.)
Instead of marking this module as `extern`, the developer should mark the module as `replaceable`.
Then, they should create a new module that `replaces` the `replaceable` module.
The developer should add the `extern` attribute to this new module.
This module's `extern` attribute will define a namespace-path-syntax-specific extern name (e.g. `.`s vs `_`s).
For each path syntax, the developer should create a separate module that `replaces` the `replaceable` module.
This TestModel demonstrates this in the `ExternV2Constructor` module and in the `WrappedTestDotNamespaced` module.

If an extern module requires per-language behavior, the extern should NOT be replaced in the path-syntax specific module.
Instead, the developer should write a new file per-language that:
1. `include`s the path-syntax specific module. (This includes any shared extern definitions in the target language.)
2. `replaces` the `replaceable` extern module. Here, the developer can add Dafny code specific to the language under generation.
   This TestModel demonstrates this in the `SimpleExternV2` module.

(TODO: Implement this)
Under this V2 system, Smithy-Dafny generated Dafny code will not declare modules as extern.
These modules will instead be given a language-idiomatic extern name through the `outer-module` compile flag.
(This is not implemented yet. The `outer-module` flag is not available on the legacy Dafny CLI. We can either migrate Smithy-Dafny's Makefile to `dafny translate` or migrate the `outerModule` flag to the legacy Dafny CLI.)

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
