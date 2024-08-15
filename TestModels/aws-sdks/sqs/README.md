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

The use of projections is demo'd by this test model; currently the projection `list-queues-and-add-permission-only` is being used.
This projection reduces the SQS model to a minimum set of shapes required in order for the ListQueues sanity test to pass.
The `AddPermission` operation is included due to a bug where models without errors do not generate valid .NET code (see [Github Issue 439](https://github.com/smithy-lang/smithy-dafny/issues/439) for more details).

## Build

### Dafny + .NET

Building a Dafny + .NET client for SQS (to demonstrate how the Smithy plugins work):

```
gradle build
```

The generated client package will appear in `build/smithyprojections/sqs/source/dafny-client-codegen`.

You can also use the traditional `make polymorph_dafny` and `make polymorph_dotnet` commands instead.

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
