# smithy-dafny-codegen

This library supports the standard Smithy workflow
for generating a Dafny client for a given Smithy model,
as described in the
[Smithy codegen docs](https://smithy.io/2.0/guides/using-code-generation/generating-a-client.html).

*WARNING: All internal and external interfaces are considered unstable and subject to change without notice.*

The file layout of the library follows the
[Codegen repo layout](https://smithy.io/2.0/guides/building-codegen/creating-codegen-repo.html#codegen-repo-layout)
described in the Smithy documentation.

Most configuration (e.g. `config`) and build files (e.g. `build.gradle.kts`)
were adapted from the corresponding files in the
[smithy-typescript](https://github.com/awslabs/smithy-typescript)
and/or
[smithy-go](https://github.com/aws/smithy-go/tree/main/codegen)
repositories.

## Generating a client

This repository builds Dafny declarations and Dafny clients from Smithy
models.

For now the library only supports AWS service models,
since the implementation will generate both Dafny code and target language code
to wrap existing AWS SDKs.
This means only services with the `aws.api#service` trait are supported.

The `TestModel/sqs` package in this repo is an example of
how to build a Dafny client. The steps needed to build a Dafny client
are as follows:

1. Create a new directory for your package. For example, "foo-client".

2. Create a `build.gradle.kts` file with the following contents:

   ```kotlin
    buildscript {
        repositories {
            mavenCentral()
        }
        dependencies {
            "classpath"("software.amazon.smithy:smithy-cli:1.28.1")
        }
    }

    plugins {
        id("software.amazon.smithy").version("0.6.0")
    }

    repositories {
        mavenLocal()
        mavenCentral()
    }

    dependencies {
        implementation("software.amazon.smithy:smithy-model:1.28.1")
        implementation("software.amazon.smithy:smithy-aws-traits:1.28.1")
        implementation("software.amazon.smithy.dafny:smithy-dafny-codegen:0.1.0")
    }
   ```

   You may need additional Smithy dependencies depending on what Smithy features
   your service model depends on, such as AWS-specific traits.
   See https://smithy.io/2.0/guides/using-code-generation/index.html for more examples.

3. Clone the GitHub repository for [smithy-dafny](https://github.com/awslabs/smithy-dafny)
   somewhere nearby, being sure to initialize submodules.
   If this repository is still private, reach out to aws-arg-dafny@amazon.com.
      
   This is necessary because it contains reusable Dafny code that
   the generated client will depend on, but is not yet independently distributed for
   shared use.

4. Create a `smithy-build.json` file with the following contents,
   substituting "smithy.example#ExampleService" with the name of the service
   to generate a client for, and specifying the set of target languages
   to support in the generated client (currently limited to "dotnet" and/or "java"):

   ```json
    {
        "version": "1.0",
        "plugins": {
            "dafny-client-codegen": {
                "service": "smithy.example#ExampleService",
                "targetLanguages": ["dotnet"],
                "includeDafnyPath": "[relative]/[path]/[to]/smithy-dafny/TestModels/dafny-dependencies/StandardLibrary/src/Index.dfy"
            }
        }
    }
   ```

5. Create a directory named `model`. This is where all of your Smithy models
   will go.

6. Copy the model for the service into the `model` directory.
   The Smithy models for AWS services can be found in several Smithy-based SDK projects,
   such as
   https://github.com/aws/aws-sdk-js-v3/tree/main/codegen/sdk-codegen/aws-models.

7. Run `gradle build` (alternatively, you can use a
   [Gradle wrapper](https://docs.gradle.org/current/userguide/gradle_wrapper.html)).

8. The generated client can be found in `build/smithyprojections/foo-client/source/dafny-client-codegen`.

See [the Smithy documentation](https://smithy.io/2.0/guides/building-models/gradle-plugin.html)
for more information on building Smithy projects with Gradle.

## Using projections

This plugin does not yet handle all Smithy features, especially since
at the time of writing this, Dafny itself does not have a strongly
idiomatic representation for concepts such as Timestamps.
Fortunately, the Smithy Gradle plugin provides several
["transforms"](https://smithy.io/2.0/guides/building-models/build-config.html#transforms)
that can be used to filter a service model
to remove unsupported shapes.

The following example removes all operations that transitively refer
to some of the shape types that this plugin does not yet support:

```json
{
    "version": "1.0",
    "projections": {
        "dafny-supported": {
            "transforms": [
                {
                    "name": "excludeShapesBySelector",
                    "args": {
                        "selector": "operation :test(~> timestamp, double, float)"
                    }
                }
            ]
        }
    },
    "plugins": {
        "dafny-client-codegen": {
            "service": "smithy.example#ExampleService",
            "targetLanguages": ["dotnet"],
            "includeDafnyPath": "[relative]/[path]/[to]/smithy-dafny/TestModels/dafny-dependencies/StandardLibrary/src/Index.dfy"
        }
    }
}
```

Refer to the Smithy documentation for more information about other transforms
that might be useful, but bear in mind that removing arbitrary shapes may lead
to a client that will fail to compile or not function correctly.