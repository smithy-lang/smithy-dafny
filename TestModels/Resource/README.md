# Resource

This project tests [smithy-dafny's](../../codegen/smithy-dafny-codegen-cli) support
for the smithy shape
[resource](https://smithy.io/1.0/spec/core/model.html#resource)
and the associated operations in `dafny` and `.NET`.

## What is under test?

The `resource` shape causes smithy-dafny to generate a Class
(or the language's equivalent)
along with methods for all of a resource's operations.

In Dafny, there is no such thing as an abstract class,
so smithy-dafny generates a Trait that describes the class.

Users than implement a Dafny class that extends this trait.

The smithy-dafny expectation is that the behavior of this class
will be entirely defined in the Dafny implementation.

(Even if this expectation is not true, any Native logic
would be referenced via a Dafny extern,
and still only exposed via the Dafny implementation).

As such, the Non-Dafny generated classes are merely wrappers
to the Dafny implementation,
providing input validation, conversion of the input or output,
and protecting the Dafny implementation from unknown exceptions
that would violate Dafny's Formal Verification assumptions.

## Build

### Dafny

1. Generate the Abstract Dafny code

```
make polymorph_dafny
```

2. Validate the manually written Dafny Code

```
make verify
```

### .NET

1. Generate the Wrappers using `polymorph`

```
make polymorph_dotnet
```

2. Transpile the tests (and implementation) to the target runtime.

```
make transpile_net
```

3. Generate the executable in the .NET and execute the tests

```
make setup_net format_net test_net
```

## Development

1. To add another target runtime support,
   edit the `Makefile` and add the appropriate recipe to
   generate the `polymorph` wrappers, and Dafny transpilation.
2. Provide any glue code between dafny and target runtime if required.
3. Build, execute, and test in the target runtime.
