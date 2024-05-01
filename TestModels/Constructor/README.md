# SimpleConstructor

This project utilizes the polymorph's localService `Config` structure in smithy to pass around values to a `Constructor` in dafny. This tests the close-to-production scenario where a client might be initilized with a set of config, and the behvior of the client is based on these values passed to the constructor.

## Build

### All target runtimes

1. Generate Dafny code using `polymorph`

```
make polymorph_dafny
```

### .NET

1. Generate the Wrappers using `polymorph`

```
make polymorph_dotnet
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

_Example_

`--output-dotnet <PATH>` in the `gradlew run` is used to generate the polymorph wrappers. Similarly `--compileTarget:<RUNTIME>` flags is used in dafny recipe to transpile to C#.
