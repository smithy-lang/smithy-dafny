# OrphanedShapes

## Background

This project tests for support of "orphaned" shapes.

An "orphaned" is a shape that exists in a Smithy model, but is not discovered by Smithy-Core's shape discovery logic.

Smithy-Core will only discover and generate code for shapes that are attached to a service via the service's

1. Operations
2. Mixins
3. Errors

and recursive traversals of the connected shapes.

If a shape is defined in a Smithy model,
but not declared in a LocalService's operations or errors
(or recursive traversals of these),
codegens that use Smithy-Core's shape discovery will not generate code for the shape.
(Similar for mixins, but Polymorph doesn't have any usage of these at the moment.)

Smithy-Dafny .NET and Java generate code for orphaned shapes because these codegens don't use Smithy-Core's shape discovery logic.

By default, any language extending a "real" Smithy code generator use Smithy-Core's shape discovery logic, and do not support orphaned shapes.

The expectation is that code is generated for orphaned shapes.
The generated code must include any class definitions and Dafny/native conversions.

## Prerequisites

This TestModel assumes these other TestModels are passing:

- Extern
- Extendable
- Errors
- LocalService
- Union
- Aggregate
- Enum

and these TestModels' prerequisite TestModels.

## Coverage

This TestModel tests some instances of orphaned shapes

- LocalService Config shapes. (Config shapes are "orphaned", but are likely already handled as one-offs by any codegen that's this TestModels' prerequisites)
- Errors
- Resources (with @aws.polymorph#reference trait) and their operations
- Structures (and structures' members)

The bar this TestModel establishes is "if a shape is defined in a Smithy model, its native/Dafny shapes and their conversions are defined in a runtime."

This TestModel asserts this by requiring externs to pass orphaned shapes across the Dafny layer.
The extern implementations MUST call Polymorph-generated native shapes and Dafny/native conversions for these orphaned shapes.
Polymorph will only generate these shapes and conversions if the language's codegen supports orphaned shapes.
