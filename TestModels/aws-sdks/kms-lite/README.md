# AWS-SDK-KMS-LITE

This project tests the [AWS KMS](https://aws.amazon.com/kms/) Operations `Encrypt, Decrypt, and GenerateDataKey` in `dafny`. The project utilizes the `aws-sdk-kms smithy model` to generate the dafny types using `polymorph`. This interface is then used in the dafny to call the appropriate operations. The actual implementation of the KMS Operations are provided by the native runtime. These integration tests aim to verify the correctness of the polymorph generated code and is run either as CI actions or manually.

Unlike the other KMS test model, this one uses a [Smithy transform](https://smithy.io/2.0/guides/smithy-build-json.html#transforms)
to project the Smithy model down to just the operations we use in downstream projects.
This demonstrates how to use a projection in a `smithy-dafny` project when necessary
(and this can be helpful to avoid unsupported shapes and traits),
but also provides a much smaller code generation target
when building new language support.

The `model.json` in this project comes from [here](https://github.com/aws/aws-cryptographic-material-providers-library/tree/cdd4885cb22957b04167b11d8b40edbdf4301d8d/ComAmazonawsKms/Model/kms).

## Build

### .NET

1. Generate the Wrappers using `polymorph`

```
make polymorph_dafny polymorph_dotnet
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
