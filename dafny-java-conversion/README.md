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

As of Dec 4th, 2022, 
we depend on Dafny @ `nightly-2022-12-02`,
which we are calling Dafny 3.10.

At some point, Dafny will release 3.10,
and we will move onto that.

```shell
wget https://github.com/dafny-lang/dafny/releases/download/nightly/dafny-nightly-2022-12-02-edab6cc-x64-osx-10.14.2.zip 
unzip dafny-nightly-2022-12-02-edab6cc-x64-osx-10.14.2.zip 
mvn -B -ntp install:install-file \
-Dfile=dafny/DafnyRuntime.jar \
-DgroupId=dafny.lang \
-DartifactId=DafnyRuntime \
-Dversion=3.10.0 \
-DgeneratePom=true \
-Dpackaging=jar
```

### Compile src
`./gradlew assemble`

### Compile src, test, and run tests
`./gradlew build`

### Publish to Maven local
`./gradlew publishToMavenLocal`
