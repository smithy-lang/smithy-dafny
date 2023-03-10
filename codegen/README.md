# smithy-dafny-codegen

This library supports the standard Smithy workflow
for generating a Dafny client for a given Smithy model,
as described in the
[Smithy codegen docs](https://smithy.io/2.0/guides/using-code-generation/generating-a-client.html).
For now the library will only support AWS service models,
since the implementation will generate both Dafny code and target language code
to wrap existing AWS SDKs.

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
