# DafnyLib

Polymorph has some Dafny dependencies.
These modules are currently copies and should be replaced
with published libraries as Dafny gets project files
and these specific modules are published.

The include file in the Polymorph command line
should point to `std/src/Index.dfy`

There are also some additional smithy dependencies.
The `DafnyLib/model` directory should also be included
as a dependent module.
The `traits.smithy` contains the smithy definitions
of the current Polymorph specific traits.
