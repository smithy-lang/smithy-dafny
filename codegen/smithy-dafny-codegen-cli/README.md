# smithy-dafny-codegen-cli

C#/.NET, Dafny, & Java code generation for Smithy models

## How to Install

This project requires Java 17 or above.

## How to use

```bash
$ # start in project root
$ pwd
~/src/smithy-dafny/smithy-dafny-codegen-cli

$ # build
$ ./gradlew build # Alternatively, if unit tests are failing, ./gradlew assemble
BUILD SUCCESSFUL in 507ms

$ # run help
$ ./gradlew run --args="-h"

> Task :run
usage: smithy-dafny-codegen-cli
    --aws-sdk                      <optional> generate AWS SDK-style API
                                   and shims
 -d,--dependent-model <arg>        directory for dependent model file[s]
                                   (.smithy format)
 -h,--help                         print help message
    --include-dafny <arg>          <optional> files to be include in the
                                   generated Dafny
    --java-aws-sdk-version <arg>   <optional> AWS SDK for Java version to
                                   use: v1, or v2 (default)
    --local-service-test           <optional> generate Dafny that tests a
                                   local service
 -m,--model <arg>                  directory for the model file[s]
                                   (.smithy or json format).
 -n,--namespace <arg>              smithy namespace to generate code for,
                                   such as 'com.foo'
    --output-dafny <arg>           <optional> output directory for
                                   generated Dafny code
    --output-dotnet <arg>          <optional> output directory for
                                   generated .NET files
    --output-java <arg>            <optional> output directory for
                                   generated Java files


BUILD SUCCESSFUL in 839ms
3 actionable tasks: 1 executed, 2 up-to-date


$ # generate local service in Dafny, Java, & .NET
$ DAFNY_ROOT=../../../private-aws-encryption-sdk-dafny-staging
$ AwsCryptographyPrimitives_ROOT=$DAFNY_ROOT/AwsCryptographyPrimitives
$./gradlew run --args="\
    --output-dafny $AwsCryptographyPrimitives_ROOT/Model\
    --include-dafny $DAFNY_ROOT/StandardLibrary/src/Index.dfy \
    --output-dotnet $AwsCryptographyPrimitives_ROOT/runtimes/net/Generated/ \
    --output-java $AwsCryptographyPrimitives_ROOT/runtimes/java/src/main/smithy-generated \
    --model $AwsCryptographyPrimitives_ROOT/Model \
    --dependent-model $DAFNY_ROOT/model \
    --namespace aws.cryptography.primitives"
...<warn logs and other junk>
[main] INFO software.amazon.polymorph.CodegenCli - Java code generated in /.../generated-java
[main] INFO software.amazon.polymorph.CodegenCli - .NET code generated in /.../generated-dotnet
[main] INFO software.amazon.polymorph.CodegenCli - Dafny code generated in /.../model
```

You can also look at the [ServiceCodegenSmokeTest](./src/test/java/software/amazon/polymorph/smithydotnet/ServiceCodegenSmokeTest.java) as a reference for how to use the library. It reads and generates code for the [test model](./src/test/resources/model.smithy), then prints the generated code to stdout.

## Arguments

By default, nothing is generated.  
Language generation is enabled by the language's `output` argument.  
This argument also determines the directory code will be written.

## Useful Debugging expressions:

To print a `List<ParseToken>`:

```
<listVariable>.stream().map(ParseToken::text).collect(Collectors.joining(" "))
```
