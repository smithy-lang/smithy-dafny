# AWS-SDK-SQS

This project builds a Dafny SDK for [AWS SQS](https://aws.amazon.com/sqs/).
Like the similar `kms` and `ddb` projects,
it does this by generating Dafny and target language code
to wrap an existing SQS SDK in one or more target languages.
Unlike those projects, however,
this one is also intended to use the Smithy Gradle plugin to build Dafny SDK clients
in the same way that other `smithy-<language>` tools support.

NOTE: The `sqs.json` in this project was copied unmodified from https://github.com/aws/aws-sdk-js-v3/blob/main/codegen/sdk-codegen/aws-models/sqs.json on March 6, 2023.
Part of the requirements of this workflow is that you shouldn't have to manually modify models.
You should be able to use the standard [projections](https://smithy.io/2.0/guides/building-models/build-config.html#projections) feature of the Smithy Gradle plugin
to trim-down or modify a model as needed before code generation instead.

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

### Dafny + .NET

Building a Dafny + .NET client for SQS (to demonstrate how the Smithy plugins work):

```
gradle build
```

The generated client package will appear in `build/smithyprojections/sqs/source/dafny-client-codegen`.

## Development

To implement https://github.com/awslabs/polymorph/issues/151, we want to provide a similar
"dafny-client-codegen" Smithy plugin that can be configured in smithy-build.json as well.
It should produce a fully-formed, ready-to-build project under
`build/smithyprojections/dafny-client-codegen`.
This probably means emitting a Makefile with a subset of what's currently in the `SharedMakefile.mk`.

The JSON configuration for this plugin will need to accept a list of target languages.
