# Documentation

This project tests [smithy-dafny's](../../codegen/smithy-dafny-codegen-cli) support
for the [`@documentation`](https://smithy.io/2.0/spec/documentation-traits.html#smithy-api-documentation-trait) trait.

## What is under test?

`@documentation` traits are translated to comments on declarations
in the target language.
They support CommonMark markup, which is translated as needed to
target language documentation styles, such as JavaDoc.

`smithy-dafny` doesn't yet have any such logic for translating CommonMark markup.
Therefore it includes validation to check that all documentation traits
are plaintext, so that they can be emitted as-is in all languages.

Note that the Smithy IDL includes syntactic sugar for documentation comments,
for example:

```smithy
/// This is documentation about a shape.
///
/// - This is a list
/// - More of the list.
string MyString
```

These are automatically transformed into `@documentation` traits in the parsed Smithy model.

`smithy-dafny` also includes a custom `@javadoc` trait.
This trait was added purely for Java support,
but is now deprecated in favour of the `@documentation` trait from the core Smithy spec instead.
This test model includes a few uses of `@javadoc` for testing coverage,
but it should not be used in new models.

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
