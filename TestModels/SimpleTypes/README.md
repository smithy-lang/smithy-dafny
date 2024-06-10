# SimpleTypes

This package contains testbed code for Smithy [simple types](https://smithy.io/2.0/spec/simple-types.html).
Each Smithy simple type will be modelled as a directory in this package. This will provide an invariant test bed for Smithy simple types.

## Structure

Please add new project directories for simple types under the base `SimpleTypes` directory.

```
.
├── SimpleString //This is a project directory
├── SimpleBlob
├── SimpleBoolean
├── SimpleByte
├── SimpleDouble
├── SimpleEnum
├── SimpleEnumV2
├── SimpleFloat
├── SimpleLong
├── SimpleShort
├── SimpleTimestamp
...
└── README.md //This README.md
```

This is the file directory for each project (example for SimpleString). Not all sub-directories would be present in the project. Each project will only contain the files that are necessary to generate any implementation code.

```
.
├── Makefile
├── Model
│   └── SimpleString.smithy
├── README.md
├── runtimes
│   └── net
|   |   ├── SimpleString.csproj
|   |   ├── test
|   |   |   └── SimpleStringTest.csproj
│   |   └── Extern
|   |       └── WrappedSimpleStringService.cs
├── src
│   ├── Index.dfy
│   ├── SimpleStringImpl.dfy
|   └── WrappedSimpleStringImpl.dfy
└── test
    ├── SimpleStringImplTest.dfy
    └── WrappedSimpleStringTest.dfy
```
