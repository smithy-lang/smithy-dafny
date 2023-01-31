# TestModels
 This package contains various groups of models which is used to form a Test Bed for Dafny-Polymorph-Native layer.
 The idea is that we want an invariant test bed with `Write Once, Test Anywhere`
 with the `Anyhwere` part targeting different runtimes that dafny supports.
 This will give us confidence in our test cases across runtimes,
 without writing native tests (and bugs) for each of those runtimes.

## Structure

Please add new project directories under the base `TestModels` directory.
Anything which is to be re-used across all projects will go inside the `TestModels` directory as well.

```
.
├── dafny-dependencies //This has standard dafny libraries used across projects
├── SimpleTypes //This holds project directories for simple types
└── README.md //This README.md
```

## Getting Started

1. Create your project directory under `TestModels`.
1. ```cd <YOUR_PROJECT_DIRECTORY>```
1. Create the `README.md`, `Makefile`, and `Model` directory.
1. Write your `*.smithy` model in the `Model` directory.
1. Use your `Makefile` recipe to execute polymorh the generate the appropriate stubbing for the runtime target.
1. Implement the `dafny` code, build, execute, and test.

## Makefile targets

In order for each project to be tested there needs to be a standard set of targets.

### Dafny verification

All Dafny produced by Dafny-Polymorph MUST be verified.
This ensures the health of the Dafny code produced.
As well as the Dafny implemented in individual projects.

* `polymorph-dafny` -- run polymorph on the project with the `--output-dafny` to generate the Dafny shell
* `verify` -- recursively gather up `*.dfy` in the project, both the generated and implemented code
* `dafny-reportgenerator` -- runs the reportgenerator to ensure [verification stability](http://dafny.org/dafny/DafnyRef/DafnyRef#2565-debugging-unstable-verification)

### Runtime

Each runtime needs its own set of targets.
This example is written assuming that the runtime you are targeting is .NET.

* `polymorph-net` -- run polymorph on the project with `--output-dafny` and `--output-dotnet` to generate the code
* `transpile_net` -- run `dafny` to produce the native code. Remember to output both the implementation and tests.
* `setup_net` -- run any required setup. For example downloading dependencies
* `test_net` -- run the tests
