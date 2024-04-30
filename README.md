# Smithy Dafny

Smithy-based code generation tools for the [Dafny](https://dafny.org) verification-aware programming language.

To a degree these tools are similar to other Smithy code generation tools
such as [`smithy-typescript`](https://github.com/awslabs/smithy-typescript),
but as Dafny is a rather unique programming language,
these tools have a somewhat unusual implementation and feature set.
They support two main use cases to date:

## Generating Dafny AWS SDK clients

This is the typical Smithy code generation use case:
given the Smithy model for an AWS service,
generate the code necessary to build a functional client SDK library
that can make requests to that service from Dafny code.

Because Dafny supports cross-compilation to multiple target languages
(C#, Java, Javascript, Go, and Python at the time of writing this),
these code generators work by emitting code to wrap existing AWS SDK clients in each target language.
A generated Dafny client for AWS SQS targeting compilation to Java, for example,
will contain Dafny source code, Java source code,
and a dependency on a Java artifact such as `software.amazon.awssdk:sqs`.

This support is provided as a `dafny-client-codegen` Smithy build plugin
with a similar API to the other
[Smithy code generators](https://smithy.io/2.0/implementations.html#client-code-generators),
configured by entries in a `smithy-build.json` file.
See the [`codegen/smithy-dafny-codegen`](codegen/smithy-dafny-codegen) directory for
further details and examples.

## Generating multi-language libraries (a.k.a. "polymorphing")

This is a more novel use of the Smithy IDL: modeling a "service" that is implemented locally (i.e. runs client-side) instead of in a remote service.
The workflow is similar to generating a [Smithy-based server implementation](https://smithy.io/2.0/ts-ssdk/index.html):

1. Write a Smithy model that describes the API for your library,
   which by construction will be language-agnostic just as AWS service APIs are.
2. Use `smithy-dafny-codegen-cli` to generate the Dafny API "skeleton" for this model.
3. Write a Dafny implementation of the API skeleton.
4. Use `smithy-dafny-codegen-cli` to generate the glue code
   necessary to adapt the Dafny-idiomatic API to each desired target language's idiomatic API.
5. Build and publish the library for each desired target language.
6. Profit!

We refer to this idea of producing multiple versions of a library with idiomatic APIs in multiple languages as "polymorphing."
Polymorphing is particularly useful for client-side libraries,
as such libraries can make use of generated Dafny AWS SDK clients to build on top of various AWS services.

This use case is currently only implemented in the `smithy-dafny-codegen-cli` tool,
which is not yet published anywhere outside of this repository.
We'd like to provide this functionality as another Smithy build plugin in the future,
likely named something like `dafny-library-codegen`.
If you're interested in this use case we'd love to hear from you -
feel free to [cut us an issue](https://github.com/smithy-lang/smithy-dafny/issues/new)!

See the [`codegen/smithy-dafny-codegen-cli`](codegen/smithy-dafny-codegen-cli) directory for further details and examples.

## Limitations

### Completeness

The code generators in this repository do not yet support all shapes and traits in the core Smithy specification
or the related AWS traits specifications.
Even for those that are supported, the implementation does not necessarily follow all of the recommendations
in those specifications.

For example, [constraint traits](https://smithy.io/2.0/spec/constraint-traits.html) are intended to
be [validated in the service rather than in clients](https://smithy.io/2.0/guides/building-codegen/mapping-shapes-to-languages.html?highlight=client%20side%20validation#should-clients-enforce-constraint-traits).
The above code generators, however, map these constraints to explicit Dafny specifications
that are therefore statically checked by the Dafny verifier.
This can be helpful for proving that the calls you make to a service from Dafny code are valid,
and safely assuming response structures are valid,
with respect to a particular snapshot of that service's API constraints.
However, it also means that future service changes that should be backwards-compatible may cause your Dafny code to break.

### Runtime libraries

Like other Smithy-based code generators, these tools will emit references to
[common runtime library code](https://smithy.io/2.0/guides/building-codegen/overview-and-concepts.html#runtime-libraries).
However, at the time of writing this the Dafny ecosystem does not yet have mature package management features
to support distributing and maintaining such libraries.
An example of the required runtime functionality is located in
`TestModels/dafny-dependencies/StandardLibrary`,
but is not intended to be distributed as a shared library.
We recommend making a copy of this code in your own projects
as the copy maintained here may change in the future.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
