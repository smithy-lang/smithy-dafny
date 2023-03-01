# SimpleDouble

This project tests [Smithy-Polymorph's](../../smithy-polymorph) support 
for the smithy shape 
[double](https://smithy.io/2.0/spec/simple-types.html#double)
and the associated operations in `dafny` and `.NET`.

## What is under test?

Currently, the `double` shape is opaque in Dafny.
That is, in Dafny, Smithy-Polymorph represesents Doubles as a
`seq<uint8>` with a length of 8. 

This representation is NOT PORTABLE between runtimes/machines,
as the Endianness is not considered.

But, for a "local service", this representation is sufficent.

In .NET, Smithy-Polymorph represents the `double` shape
as a `double`, a primitve in .NET (and most languages).

As such, in .NET, Smithy-Polymorph generates a ToDafny conversion
method that serializes a .NET `double` to a `seq<uint8>`,
and a ToNative conversion that deserializes a `seq<uint8>` to `double`.

## Status
This Test Model is NOT COMPLETE, 
it still needs the Wrapped Service components.
