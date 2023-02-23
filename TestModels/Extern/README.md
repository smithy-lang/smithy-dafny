# SimpleExtern

This project tests a few simple scenarios of implementing a [dafny extern](https://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf#15). This has a `GetExtern` operation which has the implementation in the native runtime while `ExternMustError` tries to simulate the scenario where the extern implementation returns a `Failure` instead of `Success`. `UseClassExtern` lays down the paradigm on having a class constructor as an extern implementation (constructors in dafny can't throw, but underlying runtime can throw even in constructors).

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
