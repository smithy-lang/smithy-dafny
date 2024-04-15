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
1. `cd <YOUR_PROJECT_DIRECTORY>`
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

- `polymorph-dafny` -- run polymorph on the project with the `--output-dafny` to generate the Dafny shell
- `verify` -- recursively gather up `*.dfy` in the project, both the generated and implemented code
- `dafny-reportgenerator` -- runs the reportgenerator to ensure [verification stability](http://dafny.org/dafny/DafnyRef/DafnyRef#2565-debugging-unstable-verification)

### Runtime

Each runtime needs its own set of targets.
This example is written assuming that the runtime you are targeting is .NET.

- `polymorph_dotnet` -- run polymorph on the project with `--output-dafny` and `--output-dotnet` to generate the code
- `transpile_net` -- run `dafny` to produce the native code. Remember to output both the implementation and tests.
- `setup_net` -- run any required setup. For example downloading dependencies
- `test_net` -- run the tests

## Testing Patterns

This section documents testing patterns used throughout these files.
It explains testing patterns so developers understand their purpose.
It also serves to be referenced from testing files to avoid re-explaining the purpose of a test.

### Known Value Tests

The `input` variable some `Get[Type]` functions are called with is not necessarily the same `input` that is referenced within this function.
ex. The transpiled code may have copied `input` by value into this function, rather than passing it by reference.
This is runtime-dependent behavior.
We cannot test the value of `input` from outside this function; it must be tested inside the implementation.
In the example above, if the copy-by-value is incorrect, we would not know by testing it from outside of this function.

However, in order to validate the value of `input` from within this function, we must test against a known Dafny value.
This value also cannot be passed into the function.
As in the example above, this known value may also be copied by value, and potentially suffer the same mutations described above.
To validate this, we expect a unique test vector that is defined in this function.
This method is used in conjunction with a single test that always passes in the same test vector.
As a result, this `expect` validates that the `input` referenced within this function matches the expected Dafny-defined test vector.

Since this requires a new implementation that always expects a particular input vector, we create a new function for this.
This is usually called `Get[Type]KnownValueTest`.
Other than the single new `expect` statement, this function should be the same as `Get[Type]`.

### Extern Testing

Dafny often represents types using sequences.
Runtimes often implement these sequences using array-like structures.
These structures may only be a "view" of a portion of memory.
However, there is a risk that this "view" is implemented incorrectly.

For example, a Dafny blob of length 5 (think `|seq<uint8>| = 5`) may be expected to be represented as an (ex.) Java ByteSequence of length 5.
The JRE may have already allocated a large memory buffer and would expect to
allocate memory from this buffer as needed.
(This improves allocation speed performance.)
However, if the Polymorph layer is incorrect, Polymorph may accidentally request the entire memory buffer, rather than only 5 bytes.

The problem is there is no way to verify whether this has happened from within the Dafny layer.
If Dafny has modelled itself correctly, but the error is only detectable from inside the runtime, Dafny does not understand how to interact with the generated code inside the runtime to verify the size of the blob (ByteSequence) is as expected.

The solution is to revisit noted test suites after writing externs: https://sim.amazon.com/issues/CrypTool-4911. We would write test suites using externs to validate the runtime code is behaving as expected.
