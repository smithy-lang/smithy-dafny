# Dependencies

This project tests [smithy-dafny's](../../codegen/smithy-dafny-codegen-cli) support
for creating and using dependency projects.
It explicitly tests using dependency local resources and local services,
as well as errors thrown by any dependency namespace.
These tests are written in `dafny` and transpiled to the target runtimes for execution.

## What is under test?

1. **A module can create and use an externally-defined resource**

   This test takes in a SimpleResource config, creates a local SimpleResource, and tests basic operations on that resource.

2. **A module can use a reference to an externally-created dependency resource**

   This test takes in a local ExtendableResourceReference and tests basic operations on resource.
   The ExtendableResourceReference is defined in the ExtendableResource module.
   It is expected to be an ExtendableResource type tagged with a `aws.polymorph#reference` trait.

3. **A module can locally create and use
   a reference to an externally-defined local service**

   This test takes in a SimpleConstraints service and tests basic operations on service.
   The SimpleConstraints service is defined in the SimpleConstraints module.
   However, the reference trait is added locally, inside the Dependencies module.

4. **A module can wrap native exceptions from a dependency namespace
   as a native exception from this module**

   The ExtendableResourceReference throws 3 different native exception types: SimpleExtendableResources, CollectionOfErrors, and OpaqueError.
   This test validates that these errors will be caught and wrapped by a SimpleDependencies exception.

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
