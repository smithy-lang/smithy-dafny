# Extendable

This project tests [smithy-dafny's](../../codegen/smithy-dafny-codegen-cli) support
for the custom smithy trait
[extendable](https://github.com/awslabs/polymorph/blob/main-1.x/TestModels/dafny-dependencies/Model/traits.smithy#L54-L58)
and the associated operations in `dafny` and `.NET`.

The nature of `extendable` requires "native code" to fully test it.
Thus, this module is different than the other members of "TestModels",
it requires both Dafny Source and Native Code to test it.

## What is under test?

The `extendable` trait causes smithy-dafny to generate a Native Wrapper
such that a Resource implemented in Dafny can instead be implemented
in a Native Runtime while still respecting the conditions Dafny
imposes on the formally verified Dafny implementation.

The `extendable` trait is tested in two ways via this project.

1. As a customer would use the library,
   via a runtime native implementation that extends from
   the runtime base type.
2. Via nothing but Dafny and Smithy generated code,
   by the `localServiceWrapper` test utility.

Either of these tests would be sufficient to test
the `extendable` trait alone.

However, providing both tests let's us:

1. Explicitly test the feature as the customer would use it.
2. Ensures that `localServiceWrapper` works correctly.

(2.) has great merit,
as we will have to implement `localServiceWrapper` in
every language `smithy-dafny` supports.

We need evidence that an implementation of `localServiceWrapper` is
correct.

This `TestModel` provides some evidence of that.

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
