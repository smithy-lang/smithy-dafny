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

### Dafny + .NET

Building a Dafny + .NET client for SQS (to demonstrate how the Smithy plugins work):

```
gradle build
```

The generated client package will appear in `build/smithyprojections/sqs/source/dafny-client-codegen`.

## Development

To implement <https://github.com/awslabs/polymorph/issues/151>, we provide a similar
"dafny-client-codegen" Smithy plugin that can be configured in smithy-build.json as well.
It will produce a fully-formed, ready-to-build project
under `build/smithyprojections/sqs/source/dafny-client-codegen`.
This will mean emitting a Makefile with a subset of what's currently in the `SharedMakefile.mk`,
or alternatively to emit a Dafny project file (TBD).

For now, the plugin generates the same code files as the older CLI,
but does not generate all they build configuration files necessary to build the project.
This shortcoming will be addressed in a future update.
