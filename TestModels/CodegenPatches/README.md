# CodegenPatches

This project tests the feature of automatically applying patches to generated code.
While obviously discouraged, this has been necessary in practice
to account for Smithy model inaccuracies and features that aren't yet implemented
in the core code generation logic.

These files can be located at `<library-root>`/codegen-patches/<language>/dafny-<version>.patch;
the patch file matching the generated language with the highest version less than the value of `--dafny-version`
will be applied.

The easiest way to create these patches is the following workflow
(which requires that the generated code is checked in to git):

1. Generate the code using a target like `make polymorph_dafny`.
2. Apply the necessary manual edits (preferrably with marker comments to make them stand out better).
3. Commit the generated code to git.
4. Regenerate the code, passing the `--update-patch-files` option to the polymorph CLI.
   With this repository's `SharedMakefile.mk`, you can define `POLYMORPH_OPTIONS="--update-patch-files"`.
   This will extract the necessary patch to modify the generated code to match what's checked in.

## Build

### All target runtimes

1. Generate Dafny code using `polymorph`

```
make polymorph_dafny
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
make test_net
```

## Development

1. To add another target runtime support, edit the `Makefile` and add the appropriate recipe to generate the `polymorph` wrappers, and dafny transpilation.
2. Provide any glue code between dafny and target runtime if required.
3. Build, execute, and test in the target runtime.

_Example_

`--output-dotnet <PATH>` in the `gradlew run` is used to generate the polymorph wrappers. Similarly `--compileTarget:<RUNTIME>` flags is used in dafny recipe to transpile to C#.
