# Smithy Dafny

Smithy-based code generation tools for the [Dafny](https://dafny.org) verification-aware programming language.

To a degree these tools are similar to other Smithy code generation tools
such as []`smithy-typescript`](https://github.com/awslabs/smithy-typescript),
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
A generated Dafny client for AWS SQS meant for compilation to Java, for example,
will contain Dafny source code, Java source code,
and a dependency on a Java artifact such as `software.amazon.awssdk:sqs`.

This support is provided as a `dafny-client-codegen` Smithy build plugin with a similar API to the other [Smithy code generators](https://smithy.io/2.0/implementations.html#client-code-generators), configured by entries in a `smithy-build.json` file. See the [`codegen/smithy-dafny-codegen`](codegen/smithy-dafny-codegen) directory for further details and examples.

## Generating multi-language libraries (a.k.a. "polymorphing")

This is a more novel use of the Smithy IDL: modeling a "service" that is implemented locally instead of in a remote microservice.
The workflow is similar to generating a Smithy-based server implementation:

1. Write a Smithy model that describes the API for your library,
   which by construction will be language-agnostic just as AWS service APIs are.
2. Automatically Generate the API skeleton for this model in Dafny.
3. Implement this skeleton in Dafny.
4. For each desired target language, automatically generate the glue code
   necessary to adapt the Dafny-idiomatic API to that language's idiomatic API.
5. Build and publish the library for each desired target language.
6. Profit!

We refer to this idea of producing multiple versions of a library with idiomatic APIs in multiple languages as "polymorphing."
Such libraries can make use of generated Dafny AWS SDK clients to build on top of various AWS services.

This use case is currently only implemented in the `smithy-dafny-codegen-cli` tool, 
which is not yet published anywhere outside of this repository.
We'd like to provide this functionality as another Smithy build plugin in the future, 
likely named something like `dafny-library-codegen`.
If you're interested in this use case we'd love to hear from you!
See the [`codegen/smithy-dafny-codegen-cli`](codegen/smithy-dafny-codegen-cli) directory for further details and examples.

## Limitations

The code generators in this repository do not yet support all shapes and traits in the core Smithy specification
or the related AWS traits specifications.
Even for those that are supported, the implementation does not necessarily follow those specifications'
requirements and recommendations.

For example, [constraint traits](https://smithy.io/2.0/spec/constraint-traits.html) are intended to 
be [validated in the service rather than in clients](https://smithy.io/2.0/guides/building-codegen/mapping-shapes-to-languages.html?highlight=client%20side%20validation#should-clients-enforce-constraint-traits).
The above code generators, however, map these constraints to explicit Dafny specifications
that are therefore statically checked by the Dafny verifier.
This can be helpful for proving that the calls you make to a service from Dafny code are valid,
with respect to a particular snapshot of that service's API constraints,
but means that future service changes that should be backwards-compatible may cause your Dafny code to break.
The mapping of Smithy shapes to Dafny types and specifications will likely be configurable
in the future to address this.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.
