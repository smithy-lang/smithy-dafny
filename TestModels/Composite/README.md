# Composite

This project contains two Smithy model files in one TestModel.
Polymorph-generated projects are expected to be able to handle any number of Smithy model files in one project.
These model files should share their generated Dafny code.
This is not a "TestModel" per se, but is a validation that a language can handle this.

This requires the "Dependencies" TestModel to work, as the two model files have a dependency structure.

## Build
### .NET
1. Generate the Wrappers using `polymorph`
```
make polymorph_net
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