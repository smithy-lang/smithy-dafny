# Smithy Go

This directory contains a fork of [smithy-go](https://github.com/aws/smithy-go/) (under `./codegen`) but modified heavily for dafny use case.
The initial pulled in commit was: https://github.com/aws/smithy-go/commit/7f8b3b99628aa810894bd866caa1998421c807e0
but the code might not bear any resembelance to that commit.

It uses a combination of `ShapeVisitors` and `DirectedCodegen` to visit each shape and generate the types. `TypeConversion`
classes are responsible for generating the `to` and `from` conversion.

## Generating Dafny AWS SDK clients

The directory `./awssdk` has all the logic related to the aws-sdk - dafny-go generation.

## Generating Dafny Local Service clients

The directory `./localservice` has all the logic related to the local service generation.
