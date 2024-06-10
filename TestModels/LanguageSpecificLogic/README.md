# LanguageSpecificLogic

This project demonstrates generating target-language-specific code from Dafny.
This allows developers to write and **verify** Dafny code
that is only generated and run
for a particular target language.

This directory contains a basic project demonstrating how to do this.
The generated client for this TestModel contains one operation: GetRuntimeInformation.
The output of this operation has two components: `language` and `runtime`.

`language` is a string that is set from Dafny-generated code.
This code is only generated and run for a particular target language.
This allows us to use Dafny verification (`requires`/`ensures` clauses)
to validate that the `language` attribute contains some expected value.
`language` _could_ also be set from `extern` code.
However, this would prevent us from verifying its value with Dafny.

`runtime` is a string set from `extern` code.
Each language will implement some `extern` method to get language runtime information and return it.
Since this is an `extern` method, we cannot use Dafny verification
to validate that `runtime` contains some expected value.
It is not possible to make this non-`extern` since this value requires information from the runtime.

This project implements this demonstration using Dafny's `replaceable` modules feature.
This allows a developer to declare an (abstract) module as `replaceable`,
write a (concrete) module that `replaces` it,
and add language-specific behavior to the concrete module.

In addition, this project also demonstrates language-specific tests.
This allows developers to write abstract tests that are passed to every module that `replaces` a `replaceable` module.
These tests are executed once inside the context of the `replaceable` module,
and again inside the context of the module that `replaces` it.
Developers can also add language-specific tests inside the replacing module.

## Build

### .NET

1. Generate the Wrappers using `polymorph`

```
make polymorph_dafny polymorph_dotnet
```

2. Transpile the tests (and implementation) to the target runtime.

```
make transpile_net
```

3. Generate the executable in the .NET and execute the tests

```
make test_net
```

## Development

1. To add another target runtime support, edit the `Makefile` and add the appropriate recipe to generate the `polymorph` wrappers, and dafny transpilation.
2. Provide any glue code between dafny and target runtime if required.
3. Build, execute, and test in the target runtime.

_Example_

`--output-dotnet <PATH>` in the `gradlew run` is used to generate the polymorph wrappers. Similarly `--compileTarget:<RUNTIME>` flags is used in dafny recipe to transpile to C#.
