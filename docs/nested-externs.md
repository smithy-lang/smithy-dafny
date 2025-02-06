#### Modules with “nested” extern attributes

The content in this file is relevant for Smithy-Dafny Python and Go projects.

Modules with a “nested” extern attribute (“nested extern modules”) can’t be used with Python or Go.
A "nested" extern attribute has `.`s in it. (e.g. `{:extern "my.namespace.my.project.internaldafny}`).

Ideally, one wouldn’t define nested extern modules.
However, some projects that build for Java, NET, and Rust use nested extern attributes to prefix generated Dafny code with an "internal" prefix.
For legacy support, Smithy-Dafny supports using `sed` to strip away the nested extern attribute.

**Simple “nested” externs**
For an existing project `MyProject` that uses a nested extern string like `"my.namespace.my.project.internaldafny"` , the Makefile for the project should be updated as follows:

```
ENABLE_EXTERN_PROCESSING=1  # This MUST go before `include ``../``SharedMakefileV2``.``mk

include ../SharedMakefileV2.mk`

...

TYPES_FILE_PATH=Model/MyProject.dfy
TYPES_FILE_WITH_EXTERN_STRING="module {:extern \"my.namespace.my.project.internaldafny.types\" } MyProjectTypes"
TYPES_FILE_WITHOUT_EXTERN_STRING="module MyProjectTypes"

INDEX_FILE_PATH=src/Index.dfy
INDEX_FILE_WITH_EXTERN_STRING="module {:extern \"my.namespace.my.project.internaldafny\" } MyProject refines AbstractMyProjectService {"
INDEX_FILE_WITHOUT_EXTERN_STRING="module MyProject refines MyProject {"
```

This setup will work for “simple” projects that only define nested extern modules in `Index.dfy` and the types file.

Examples:

- [Constraints TestModel](https://github.com/smithy-lang/smithy-dafny/blob/main-1.x/TestModels/Constraints/Makefile). Almost all TestModels are “simple.”
- [DDB TestModel](https://github.com/smithy-lang/smithy-dafny/blob/main-1.x/TestModels/aws-sdks/ddb/Makefile). All AWS SDK projects should be simple.

**Complex “nested” externs**
Some projects use nested extern modules in files other than `Index.dfy` and the types file.
For these “complex” projects, you will need to define new sed strings _and_ override the default Makefile targets.
If you have a file `MySpecialFile.dfy` that requires sed replacement, you will need to override some targets:

```
ENABLE_EXTERN_PROCESSING=1

...

MY_SPECIAL_FILE_FILE_PATH=src/MySpecialFile.dfy
MY_SPECIAL_FILE_WITH_EXTERN_STRING="module {:extern \"my.namespace.my.special.file.internaldafny\" } MySpecialFile"
MY_SPECIAL_FILE_WITHOUT_EXTERN_STRING="module MySpecialFile"

...

# Override target; handle both the Index.dfy file and the new file
_sed_index_file_add_extern:
    $(MAKE) _sed_file SED_FILE_PATH=$(MY_SPECIAL_FILE_FILE_PATH) SED_BEFORE_STRING=$(MY_SPECIAL_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(MY_SPECIAL_FILE_WITH_EXTERN_STRING)
    $(MAKE) _sed_file SED_FILE_PATH=$(INDEX_FILE_PATH) SED_BEFORE_STRING=$(INDEX_FILE_WITHOUT_EXTERN_STRING) SED_AFTER_STRING=$(INDEX_FILE_WITH_EXTERN_STRING)

_sed_index_file_remove_extern:
    $(MAKE) _sed_file SED_FILE_PATH=$(MY_SPECIAL_FILE_FILE_PATH) SED_BEFORE_STRING=$(MY_SPECIAL_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(MY_SPECIAL_FILE_WITHOUT_EXTERN_STRING)
    $(MAKE) _sed_file SED_FILE_PATH=$(INDEX_FILE_PATH) SED_BEFORE_STRING=$(INDEX_FILE_WITH_EXTERN_STRING) SED_AFTER_STRING=$(INDEX_FILE_WITHOUT_EXTERN_STRING)
```

Examples:

- [MultipleModels TestModel](https://github.com/smithy-lang/smithy-dafny/blob/main-1.x/TestModels/MultipleModels/Makefile). Any Smithy-Dafny project with multiple local services is “Complex.”
- [Crypto Tools’ MPL](https://github.com/aws/aws-cryptographic-material-providers-library/blob/main/AwsCryptographicMaterialProviders/Makefile). This project has multiple local services, but also applies nested extern attributes to some of its other modules (SynchronizedLocalCMC and StormTrackingCMC).

The following Makefile targets exist and can be overridden:

```
_sed_types_file_remove_extern
_sed_index_file_remove_extern
_sed_wrapped_types_file_remove_extern
_sed_types_file_add_extern
_sed_index_file_add_extern
_sed_wrapped_types_file_add_extern
```
