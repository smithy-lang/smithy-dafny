# SimpleExternV2

This project tests implementing a [dafny extern](https://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf#15) using the "V2 Extern" system.
The operations on this model are identical to operations in the `Extern` TestModel, only with "V2" suffixes appended.

This V2 extern system uses the `replaceable` and `replaces` keywords to allow a module to have a unique extern name in each target language.
Under this system, the `replaceable` keyword marks a `module` that will be compiled as an `extern` `module` in a target language.
Another module `replaces` the `replaceable` module; the `replaces` module will be tagged with an `extern` whose name is idiomatic for the target language.


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
