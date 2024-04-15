# LocalService

This project tests [smithy-dafny's](../../codegen) support
for the smithy shape
[service](https://smithy.io/1.0/spec/core/model.html#service)
and the associated operations in `dafny` and `Java`.

## What is under test?

The `service` shape causes smithy-dafny to generate a Class
(or the language's equivalent)
along with methods for all of a services's operations.

Every [Test Model](../../TestModels) tests this.
However, there are some traits defined by Smithy-Dafny
that target service shapes.

In particular,
the `aws.polymorph#localService` trait introduces specific behavior
that is used by all the [Test Models](../../TestModels)
other than those under [TestModels/aws-sdks](../../TestModels/aws-sdks).

These other [Test Models](../../TestModels) do not cover all the
behavior of the `aws.polymorph#localService` trait.

The goal of this [Local Service Test Model](../../TestModels/LocalService) is to
explicitly test all the behaviors of the `aws.polymorph#localService` trait.

## Current state

Right now, only the following is tested:

- Smithy-Dafny's generated Java
  include converters for LocalServices

## TODO

Everything else part of the LocalService Trait.
Particularly:

- Smithy-Dafny's generated Java references
  LocalServices correctly in Builders

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

### Java

1. Generate the Java code

```
make polymorph_java
```

Then, either call: `make build_java test_java` or:

2. Transpile the Dafny to Java

```
make transpile_java
```

3. Compile the Smithy Generated, Dafny Generated, & Manually written Java together:

```
gradle -p runtimes/java build
```

4. Test the Java: `gradle -p runtimes/java javaTests` or:

```
make test_java
```

## Development

1. To add another target runtime support,
   edit the `Makefile` and add the appropriate recipe to
   generate the `polymorph` wrappers, and Dafny transpilation.
2. Provide any glue code between dafny and target runtime if required.
3. Build, execute, and test in the target runtime.
4. Be sure that any testing that cannot be done through pure Dafny code
   is implemented in the runtime.
