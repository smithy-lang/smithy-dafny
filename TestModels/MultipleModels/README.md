# MultipleModels

This project contains two Smithy model files in one project.
Smithy-Dafny-generated projects are expected to be able to handle any number of Smithy model files in one project; i.e.

```
└── MyProject/
    └── dafny/
        └── SubProjectA/
        │   ├── Model/
        │   │   ├── localservice-a.smithy
        │   │   ├── subproject-a-child1.smithy
        │   │   └── ... (any number of child models for localservice-a.smithy)
        │   ├── src/ # Dafny source code
        │   └── test/ # Dafny test code
        ├── SubProjectB/
        │   ├── Model/
        │   │   └── localservice-b.smithy
        │   │   ├── subproject-b-child1.smithy
        │   │   └── ... (any number of child models for localservice-b.smithy)
        │   ├── src/
        │   ├── test/
        └── SubProjectC/
            ├── Model/
            │   └── awssdk-service-c.smithy
            ├── src/
            └── test/
        ... (and so on)
```

If a single Smithy-Dafny project (ex. MyProject)
has multiple subprojects (ex. SubProjects A, B, and C), then:

1. Each subproject MUST have ONLY ONE single service shape under generation; and
2. The subprojects, their Smithy model(s), and their Dafny code MUST be laid out in this structure.
3. The project's Makefile MUST set the `DIR_STRUCTURE_V2` variable to a non-empty value.

These model files should **share** their generated Dafny implementation.
While the Dafny source code is located in separate folders,
the generated Dafny code should be **shared** across all subprojects.
**This behavior is not validated by this TestModel.**
The Smithy-Dafny developer should ensure both projects in this TestModel
refer to a **shared** Dafny implementation.

This TestModel should not require much, or any code generation work to pass.
This TestModel may require project management changes to handle multiple Model files
and/or refer to a shared Dafny implementation.

This TestModel requires the "Dependencies" TestModel as a prerequisite,
as the two model files in this project have a dependency structure.

## Build

### .NET

1. Generate the Wrappers using `polymorph`

```
make polymorph_dafny DAFNY_VERSION_OPTION="--dafny-version A.B.C" \
&& make polymorph_dotnet DAFNY_VERSION_OPTION="--dafny-version A.B.C" \
&& make polymorph_java DAFNY_VERSION_OPTION="--dafny-version A.B.C"
```

2. Transpile the tests (and implementation) to the target runtime.

```
make transpile_net && make transpile_java
```

3. Generate the executable in the .NET and execute the tests

```
make test_net && make test_java
```

## Development

1. To add another target runtime support, edit the `Makefile` and add the appropriate recipe to generate the `polymorph` wrappers, and dafny transpilation.
2. Provide any glue code between dafny and target runtime if required.
3. Build, execute, and test in the target runtime.
