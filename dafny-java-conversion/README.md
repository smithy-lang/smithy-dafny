## Dafny Java Conversion
A Java 8 Library that converts from
idiomatic Java types to Dafny-Java types and vice versa.

This library assumes that Dafny will not introduce breaking changes
to the Dafny Runtime jar inside a major version.

## Set Up
This library depends on the `DafnyRuntime.jar`. 

That `jar` is normally built/installed by 
Dafny in the Dafny Binaries folder.

I recommend developers use `mvn` to 
install the jar to their local Maven repository.

Note that the `version` should be determined by the Dafny version
your project is currently working on (`dafny /version`).

```shell
mvn install:install-file \
-Dfile=$(pwd)/DafnyRuntime.jar \
-DgroupId=dafny.lang \
-DartifactId=DafnyRuntime \
-Dversion=3.8.1 \
-DgeneratePom=true \
-Dpackaging=jar
```

### Compile src
`./gradlew assemble`

### Compile src, test, and run tests
`./gradlew build`

### Publish to Maven local
`./gradlew publishToMavenLocal`
