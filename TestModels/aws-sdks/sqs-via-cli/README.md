# AWS-SDK-SQS

This project builds a Dafny SDK for [AWS SQS](https://aws.amazon.com/sqs/).
It is a copy of the `TestModels/aws-sdks/sqs` project,
but it generates code using the older CLI instead of the newer Smithy build plugin.
This project will eventually be removed entirely as the CLI is deprecated.
For more details, please see `TestModels/aws-sdks/sqs/README.md`.

NOTE: The `sqs.json` in this project was copied almost unmodified from https://github.com/aws/aws-sdk-js-v3/blob/main/codegen/sdk-codegen/aws-models/sqs.json on March 6, 2023.
The only edit is to remove the @smithy.rules#endpointRuleSet from the service,
because it happens to be invalid and newer versions of Smithy catch this and crash.
We can't yet update the SQS model because newer versions use Smithy 2.0 enum shapes,
which we don't yet support for .NET.

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
