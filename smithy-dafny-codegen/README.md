# smithy-polymorph

C#/.NET, Dafny, & Java code generation for Smithy models

## How to Install

This project requires Java 17 or above.
It also requires the DafnyRuntime Jar,
and `dafny-java-conversion`.

Follow the instructions in `dafny-java-conversion`'s README
to install the DafnyRuntime Jar, 
and then execute `./gradlew publishToMavenLocal` to install
`dafny-java-conversion` locally.

## How to use

```bash
$ # start in project root
$ pwd
~/src/polymorph/smithy-polymorph

$ # build
$ ./gradlew build # Alternatively, if unit tests are failing, ./gradlew assemble
BUILD SUCCESSFUL in 507ms

$ # run help
$ ./gradlew run --args="-h"
usage: smithy-polymorph
    --aws-sdk                           <optional> generate AWS SDK-style
                                        API and shims
 -d,--dependent-model <arg>             directory for dependent model
                                        file[s] (.smithy format)
 -h,--help                              print help message
    --include-dafny <arg>               <optional> file to be include in
                                        the Dafny model file
 -m,--model <arg>                       directory for the model file[s]
                                        (.smithy format). Also the Dafny
                                        output directory.
 -n,--namespace <arg>                   smithy namespace to generate code
                                        for, such as 'com.foo'
    --output-dafny                      <optional> generate Dafny code
    --output-dotnet <arg>               <optional> output directory for
                                        generated .NET files
    --output-java <arg>                 <optional> output directory for
                                        generated Java files
    --output-local-service-test <arg>   <optional> output directory for
                                        generated Dafny that tests a local
                                        service


BUILD SUCCESSFUL in 839ms
3 actionable tasks: 1 executed, 2 up-to-date


$ # generate local service in Dafny, Java, & .NET
$ DAFNY_ROOT=../../private-aws-encryption-sdk-dafny-staging
$ AwsCryptographyPrimitives_ROOT=$DAFNY_ROOT/AwsCryptographyPrimitives
$./gradlew run --args="\
    --output-dafny \
    --include-dafny $DAFNY_ROOT/StandardLibrary/src/Index.dfy \
    --output-dotnet $AwsCryptographyPrimitives_ROOT/runtimes/net/Generated/ \
    --output-java $AwsCryptographyPrimitives_ROOT/runtimes/java/src/main/smithy-generated \
    --model $AwsCryptographyPrimitives_ROOT/Model \
    --dependent-model $DAFNY_ROOT/model \
    --namespace aws.cryptography.primitives"
...<warn logs and other junk>
[main] INFO software.amazon.smithy.dafny.codegen.CodegenCli - Java code generated in /.../generated-java
[main] INFO software.amazon.smithy.dafny.codegen.CodegenCli - .NET code generated in /.../generated-dotnet
[main] INFO software.amazon.smithy.dafny.codegen.CodegenCli - Dafny code generated in /.../model
```

You can also look at the [ServiceCodegenSmokeTest](./src/test/java/software/amazon/polymorph/smithydotnet/ServiceCodegenSmokeTest.java) as a reference for how to use the library. It reads and generates code for the [test model](./src/test/resources/model.smithy), then prints the generated code to stdout.

## Arguments
By default, nothing is generated.  
Language generation is enabled by the language's `output` argument.  
For `dotnet` and `java`, this argument also determines the directory code will be written.  
For `dafny`, by default, the code will be written to the `model` directory.
If the `output-local-service-test` option is provided,
the Dafny code will be written there.


## Useful Debugging expressions:

To print a `List<ParseToken>`:
```
<listVariable>.stream().map(ParseToken::text).collect(Collectors.joining(" "))
```
