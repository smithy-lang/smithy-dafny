# AggregateReferences

This project implements tests for "aggregate references".
These are shapes with an `@reference` trait that are nested in layers of structures, lists, and maps.
These should be tested separately from both the Aggregate and Resource modules,
as this depends on code generation for both of those modules being implemented to succeed.
Once both of those modules' test models are passing for a given language,
this module SHOULD work without issue.

These shapes require unique code generation for the Dafny `requires`/`modifies`/`ensures` clauses.
Right now, this logic is implemented for local service code generators, but not for operations code generators.
Effectively, Smithy-Dafny does not support generating `requires`/`modifies`/`ensures` clauses
for operations whose inputs or outputs contain references nested inside multiple lists, maps, and structures.

This module only contains Dafny verification
There is no runtime test for these,
as the unique code generation is only Dafny code.
It would be nice to add runtime validation for this, but this has not been done at this time.

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

## Development
1. To add target runtime support,
   edit the `Makefile` and add the appropriate recipe to
   generate the `polymorph` wrappers, and Dafny transpilation.
2. Provide any glue code between dafny and target runtime if required.
3. Build, execute, and test in the target runtime.
