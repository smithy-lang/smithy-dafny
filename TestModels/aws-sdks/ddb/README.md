# AWS-SDK-DDB

This project tests the [AWS DynamoDB](https://aws.amazon.com/dynamodb/) Operations `QUERY, GET, and PUT` in `dafny`. The project utilizes the `aws-sdk-ddb smithy model` to generate the dafny types using `polymorph`. This interface is then used in the dafny to call the appropriate operations. The actual implementation of the DynamoDB Operations are provided by the underlying native runtime. These integration tests aim to verify the correctness of the polymorph generated code and is run either as CI actions or manually.

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