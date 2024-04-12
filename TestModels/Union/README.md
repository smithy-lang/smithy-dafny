# SimpleConstructor

This project implements the smithy type [Union](https://smithy.io/2.0/spec/aggregate-types.html#union) and the associated operations in `dafny`. This is then transpiled to a target runtime, and each tests are executed - either as CI actions or manually.

NOTE: Union field names need to start with a capital letter. Otheriwse this causes a mismatch in the dafny generated method and polymorph generated calls in the .NET runtime. https://github.com/awslabs/polymorph/issues/145

Example:

```
union MyUnion {
    IntegerValue: Integer,
    StringValue: String
}
```

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
