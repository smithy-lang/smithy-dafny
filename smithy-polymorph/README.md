# smithy-polymorph

C#/.NET, Dafny, & Java code generation for Smithy models

## How to use

This project requires Java 17 or above.

```bash
$ # start in project root
$ pwd
~/src/polymorph/smithy-polymorph

$ # build
$ ./gradlew build
BUILD SUCCESSFUL in 507ms

$ # run help
$ ./gradlew run --args="-h"
usage: smithy-polymorph
    --aws-sdk                       <optional> generate AWS SDK-style API
                                    and shims
 -d,--dependent-model <arg>         directory for dependent model file[s]
                                    (.smithy format)
 -h,--help                          print help message
    --include-dafny <arg>           <optional> file to be include in the
                                    Dafny model file
 -m,--model <arg>                   directory for the model file[s]
                                    (.smithy format). Also the Dafny
                                    output directory.
 -n,--namespace <arg>               smithy namespace to generate code for,
                                    such as 'com.foo'
    --output-dafny
    --output-dotnet <arg>           <optional> output directory for
                                    generated .NET files
    --output-java <arg>             <optional> output directory for
                                    generated Java files
    --wrapped-local-service <arg>    <optional> generate wrapped codegen
                                    and shims for an existing local
                                    service. The argument is the path to
                                    output Dafny. This MUST be in the
                                    `Model` directory of the project.


BUILD SUCCESSFUL in 839ms
3 actionable tasks: 1 executed, 2 up-to-date


$ # generate code
$ OUTPUT_DOTNET=/path/to/generated_dotnet
$ OUTPUT_JAVA=/path/to/generated_java
$ OUTPUT_DAFNY=/path/to/generated_dafny
$ MODEL=src/test/resources/model.smithy
$ DEPENDENT=src/test/resources/
$ SERVICE='polymorph.demo#StringLists'
$ ./gradlew run --args="--output-dotnet $OUTPUT_DOTNET --output-java $OUTPUT_JAVA --output-dafny -m $MODEL -d $DEPENDENT"
...<warn logs and other junk>
[main] INFO software.amazon.polymorph.CodegenCli - Java code generated in /.../generated-java
[main] INFO software.amazon.polymorph.CodegenCli - .NET code generated in /.../generated-dotnet
[main] INFO software.amazon.polymorph.CodegenCli - Dafny code generated in /.../model
```

You can also look at the [ServiceCodegenSmokeTest](./src/test/java/software/amazon/polymorph/smithydotnet/ServiceCodegenSmokeTest.java) as a reference for how to use the library. It reads and generates code for the [test model](./src/test/resources/model.smithy), then prints the generated code to stdout.

## Arguments
By default, nothing is generated.  
Language generation is enabled by the language's `output` argument.  
For `dotnet` and `java`, this argument also determines the directory code will be written.  
For `dafny`, the code will always be written to the `model` directory.

## Manual build steps for .NET

Temporary manual steps for getting the generated code into the .NET ESDK.
Soon this will be replaced by a real Polymorph build process.

First export some variables indicating where your ESDK model and .NET ESDK live:

```bash
export MODEL_ROOT=  # e.g. ~/src/aws-encryption-sdk-dafny/model
export DOTNET_ROOT= # e.g. ~/src/aws-encryption-sdk-dafny/aws-encryption-sdk-net-formally-verified
export DAFNY_ROOT=  # e.g. ~/src/aws-encryption-sdk-dafny
```

Then, run the following. You'll likely see a bunch of warnings about "Overwriting existing file".

```bash
# Generate code for material providers
# NOTE: No Dafny code will be generated, since Dafny codegen doesn't currently support non-AWS-SDK models
./gradlew run --args="\
    --output-dotnet $DOTNET_ROOT/Source/API/Generated/Crypto \
    --output-dafny $DAFNY_ROOT/src/Generated \
    -m $MODEL_ROOT -s aws.encryptionSdk.core#AwsCryptographicMaterialProvidersFactory"

# Generate code for KMS
./gradlew run --args="\
    --output-dotnet $DOTNET_ROOT/Source/API/Generated/Kms \
    --output-dafny $DAFNY_ROOT/src/Generated \
    --aws-sdk \
    -m $MODEL_ROOT -s com.amazonaws.kms#KeyManagementService"

# Generate code for ESDK
# NOTE: No Dafny code will be generated, since Dafny codegen doesn't currently support non-AWS-SDK models
./gradlew run --args="\
    --output-dotnet $DOTNET_ROOT/Source/API/Generated/Esdk \
    --output-dafny $DAFNY_ROOT/src/Generated \
     -m $MODEL_ROOT -s aws.encryptionSdk#AwsEncryptionSdkFactory"
```

Confirm the files were generated as expected:

```bash
ls $DOTNET_ROOT/Source/API/Generated/Crypto
ls $DAFNY_ROOT/src/Generated
```

## Useful Debugging expressions:

To print a `List<ParseToken>`:
```
<listVariable>.stream().map(ParseToken::text).collect(Collectors.joining(" "))
```
