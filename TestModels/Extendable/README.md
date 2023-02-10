# Extendable

This project tests [Smithy-Polymorph's](../../smithy-polymorph) support 
for the custom smithy trait 
[extendable](https://github.com/awslabs/polymorph/blob/main-1.x/TestModels/dafny-dependencies/Model/traits.smithy#L54-L58) 
and the associated operations in `dafny` and `.NET`.

The nature of `extendable` requires "native code" to fully test it.
Thus, this module is different than the other members of "TestModels",
it requires both Dafny Source and Native Code to test it.

## What is under test?
The `extendable` trait causes Smithy-Polymorph to generate a Native Wrapper
such that a Resource implemented in Danfy can instead be implemented
in a Native Runtime while still respecting the conditions Dafny 
imposes on the formally verified Dafny implementation.

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
make polymorph_net
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
