# TestModels
 This package contains various models which is used to form a Test Bed for Dafny-Polymorph-Native layer.
 The idea is that we want an invariant test bed with `Write Once, Test Anywhere`
 with the `Anyhwere` part targeting different runtimes that dafny supports.
 This will give us confidence in our test cases across runtimes,
 without writing native tests (and bugs) for each of those runtimes.

## Structure

Please add new project directories under the base `TestModels` directory.
Anything which is to be re-used across all projects will go inside the `TestModels` directory as well.

```
.
├── DafnyLib //This has standard dafny libraries used across projects
├── README.md //This README.md
└── String //This is a project directory
```

This is how a project would look like (not all sub-driectories be present).
```
.
├── Makefile
├── Model
│   ├── SimpleTypesStringTypes.dfy
│   ├── SimpleTypesStringTypesWrapped.dfy
│   └── String.smithy
├── README.md
├── runtimes
│   └── net
├── src
│   ├── Index.dfy
│   └── SimpleStringImpl.dfy
└── test
    ├── SimpleStringImplTest.dfy
    ├── WrappedSimpleStringImpl.dfy
    └── WrappedSimpleStringTest.dfy
```

## Getting Started

1. Create your project directory under `TestModels`.
1. ```cd <YOUR_PROJECT_DIRECTORY>```
1. Create the `README.md`, `Makefile`, and `Model` directory.
1. Write your `*.smithy` model in the `Model` directory.
1. Use your `Makefile` recipe to execute polymorh the generate the appropriate stubbing for the runtime target.
1. Implement the `dafny` code, build, execute, and test.