# SimpleDouble

This project tests [smithy-dafny's](../../codegen/smithy-dafny-codegen-cli) support
for the smithy shape
[double](https://smithy.io/2.0/spec/simple-types.html#double)
and the associated operations in `dafny` and `.NET`.

## What is under test?

Currently, the `double` shape should be treated as opaque in Dafny.
In Dafny, smithy-dafny represesents Doubles as a
`seq<uint8>` with a length of 8.

This representation is NOT PORTABLE between runtimes/machines,
as the Endianness is not considered.

But, for a "local service", this representation is sufficent.

In .NET, smithy-dafny represents the `double` shape
as a `double`, a primitve in .NET (and most languages).

As such, in .NET, smithy-dafny generates a ToDafny conversion
method that serializes a .NET `double` to a `seq<uint8>`,
and a ToNative conversion that deserializes a `seq<uint8>` to `double`.

## Status

The test model is sufficent for a "local service",
as long as NO operations are committed on the double
via Dafny code.

Once we:

1. Implement a [Global Dafny Double defination](https://github.com/aws/private-aws-encryption-sdk-dafny-staging/issues/120)
2. Refactor the [Runtime serialization of Double's to Dafny Bytes such that they are all consistent](https://github.com/awslabs/polymorph/issues/123)
3. We can add a `GetDoubleKnownValueTest` operation to this test model, and verify that.

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
   edit this `Makefile` (or the `SharedMakefile.mk`) and
   add the appropriate recipe to
   generate the `polymorph` wrappers, and Dafny transpilation.
2. Provide any glue code between dafny and target runtime if required.
3. Build, execute, and test in the target runtime.
