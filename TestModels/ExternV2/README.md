# SimpleExternV2

This project tests implementing a [dafny extern](https://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf#15) using the "V2 Extern" system.
This models and its shapes are identical to operations in the `Extern` TestModel, only with "V2" suffixes appended.

This V2 extern system uses the `replaceable` and `replaces` keywords in conjunction with the `outer-module` compile flag to allow a module to have idiomatic extern names in each target language.

Under this V2 system, manually-written Dafny source code should mark `module`s that are intended to be `extern` as `replaceable`.
Another manually-written module `replaces` the `replaceable` module;
The `replaces` module will be tagged with an `extern` whose name is idiomatic for the target language.

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
