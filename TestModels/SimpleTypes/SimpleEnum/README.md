# SimpleEnum

This project will implement the smithy type [enum](https://smithy.io/2.0/spec/simple-types.html#enum) and the associated operations in `dafny`.

## Status

This project does not fully build for Dotnet. We can generate the Dafny and Dotnet code, but the generated Dotnet code does not contain the generated enum values. (This might be an issue with the Smithy model too). As a result, running `make test_net` yields errors:

```
...polymorph/TestModels/SimpleTypes/SimpleEnum/runtimes/net/Generated/TypeConversion.cs(21,58): error CS0117: 'SimpleEnum' does not contain a definition for 'FIRST' [/...polymorph/TestModels/SimpleTypes/SimpleEnum/runtimes/net/SimpleEnum.csproj]
...polymorph/TestModels/SimpleTypes/SimpleEnum/runtimes/net/Generated/TypeConversion.cs(22,59): error CS0117: 'SimpleEnum' does not contain a definition for 'SECOND' [/...polymorph/TestModels/SimpleTypes/SimpleEnum/runtimes/net/SimpleEnum.csproj]
...polymorph/TestModels/SimpleTypes/SimpleEnum/runtimes/net/Generated/TypeConversion.cs(23,58): error CS0117: 'SimpleEnum' does not contain a definition for 'THIRD' [/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleEnum/runtimes/net/SimpleEnum.csproj]
```

We would need to modify the Smithy model in some way, or update Dotnet code generator to generate enum values.

## Build

## Build
### .NET
1. Generate the Wrappers using `polymorph`
```
make generate_polymorph
```

2. Transpile the tests (and implementation) to the target runtime.
```
make transpile_net
```

3. Generate the executable in the .NET. This does *not* work; we would need to debug either the Smithy model or the Dotnet code generator to generate the enum values for this to work.
```
make test_net
```