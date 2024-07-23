# Positional

This project tests [smithy-dafny's](../../codegen/smithy-dafny-codegen-cli) support
for the custom smithy trait
[positional](https://github.com/smithy-lang/smithy-dafny/blob/main-1.x/TestModels/dafny-dependencies/Model/traits.smithy#L37-L51).

## What is under test?

The `positional` trait causes smithy-dafny to avoid
the extra indirection of an input or output structure for an operation.
It offers a tradeoff: a simpler and more idiomatic user experience,
at the expense of not being able to add more members to the structure in the future
without breaking existing callers.

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
