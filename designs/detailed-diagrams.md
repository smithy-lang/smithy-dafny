# Detailed design diagrams

These are detailed design diagrams
used to flush out ideas
in smithy-dafny.

## Dependencies

Dependencies are a problem for Dafny
because by default Dafny includes all code
into a single program.
Dafny then translates all this code
into a single program.
This is illustrated in following diagram.
The difficulty here is that when A and C
try and exist in the same environment,
then B symbols will be duplicated.
Because B is a Dafny library
when it compiles it will produce
the same symbols again.

```mermaid
---
title: Dafny default Dependencies inside
---
graph LR

subgraph Dafny
  A -->|Dependency| B
  C -->|Dependency| B

end

subgraph Java
  subgraph JavaA["A<sub>java</sub>"]
    JavaAB[B<sub>java</sub>]
  end

  subgraph JavaC["C<sub>java</sub>"]
    JavaCB[B<sub>java</sub>]
  end
end

subgraph Net[.Net]
  subgraph NetA["A<sub>.net</sub>"]
    NetAB[B<sub>.net</sub>]
  end

  subgraph NetC["C<sub>.net</sub>"]
    NetCB[B<sub>.net</sub>]
  end
end

subgraph Js[Javascript]
  subgraph JsA["A<sub>js</sub>"]
    JsAB[B<sub>js</sub>]
  end

  subgraph JsC["C<sub>js</sub>"]
    JsCB[B<sub>js</sub>]
  end
end

Dafny ---> Java
Dafny ---> Net
Dafny ---> Js
```

However organizing code required packages and dependencies.
Looking at how the AWS Encryption SDK (ESDK)
packages its dependencies.
This is a natural way for code to be organized.
Having duplicate symbols
for the `Crypto` library would be problematic.

```mermaid
---
title: Complex Dependencies
---
graph LR

subgraph Dafny
  ESDK

  ESDK -->|Dependency| MaterialProviders
  ESDK -->|Dependency| Crypto
  MaterialProviders -->|Dependency| Crypto
end

subgraph Java
  JavaESDK["ESDK<sub>java</sub>"]
  JavaCrypto["Crypto<sub>java</sub>"]
  JavaMaterialProviders["JavaMaterialProviders<sub>java</sub>"]

  Application -->|Unverified| JavaESDK
  Application -->|Unverified| JavaMaterialProviders

  JavaESDK -->|Verified| JavaCrypto
  JavaESDK -->|Verified| JavaMaterialProviders
  JavaMaterialProviders -->|Verified| JavaCrypto
end

Dafny --> Java

```

Now let us return to our first example
and model the dependencies outside the translated program.
In this way when the Dafny is translated
the dependency information is not lost.
This will require coordinating dependencies
between the Dafny and the Native runtime.

```mermaid
---
title: Dafny with dependencies expressed in native
---
graph LR

subgraph Dafny

  A -->|Dependency| B
  C -->|Dependency| B
end

subgraph Java
  JavaA["A<sub>java</sub>"]
  JavaC["C<sub>java</sub>"]
  JavaB["B<sub>java</sub>"]

  JavaA -->|Dependency| JavaB
  JavaC -->|Dependency| JavaB
end

subgraph Net[".Net"]
  NetA["A<sub>.net</sub>"]
  NetB["B<sub>.net</sub>"]
  NetC["C<sub>.net</sub>"]

  NetA -->|Dependency| NetB
  NetC -->|Dependency| NetB
end

subgraph Js["Javascript"]
  JsA["A<sub>js</sub>"]
  JsB["B<sub>js</sub>"]
  JsC["C<sub>js</sub>"]

  JsA -->|Dependency| JsB
  JsC -->|Dependency| JsB
end

Dafny ---> Java
Dafny ---> Net
Dafny ---> Js
```

## Smithy Dafny

### Library Development

Here is a example of the various components
of smithy dafny fit together to translate a library.

```mermaid
---
title: How smithy-dafny packages a Dafny Implementation
---
graph LR

subgraph Legend
  direction LR
  start1[ ] --->|Depends on| stop1[ ]
  style start1 height:0px;
  style stop1 height:0px;
  start2[ ] ===>|Dafny translation to native code| stop2[ ]
  style start2 height:0px;
  style stop2 height:0px;
  start3[ ] -..->|smithy-dafny codegen| stop3[ ]
  style start3 height:0px;
  style stop3 height:0px;
  start4[ ] --->|Testing| stop4[ ]
  style start4 height:0px;
  style stop4 height:0px;
end
linkStyle 1 stroke:blue;
linkStyle 3 stroke:red;

subgraph Smithy
  AModel["Model for A"]
end

subgraph Dafny
  subgraph A["Package for A"]
    ATypes["Dafny Types for A"]
    AInterface["Dafny Interface for A"]
    AImplementation["Dafny implementation of A"]

    AImplementation --> AInterface
    ATypes --> AInterface
    ATypes --> AImplementation

    AModel -.-> ATypes
    AModel -.-> AInterface
  end

  subgraph ATests["Tests for A"]
    AUnitTests["Unit Tests for A"]
    AIntegrationTests["Integration Tests for A"]

    AUnitTests -->  AImplementation
    AIntegrationTests --> AInterface
  end
end

subgraph Net[".Net"]
  subgraph NetA["A<sub>.net</sub>"]
    NetAFromDafny
    NetATypes
    NetAInterface
    NetATypeConversion["To/From Dafny"]

    NetATypeConversion --> NetAInterface
    NetAFromDafny --> NetAInterface
    NetATypes --> NetAInterface
    NetATypes --> NetATypeConversion
    AModel -.-> NetATypes
    AModel -.-> NetAInterface
    AModel -.-> NetATypeConversion
    A ==> NetAFromDafny
  end

  NetATests

  ATests ==> NetATests
  NetATests --> NetAFromDafny
end

linkStyle 9 stroke:red;
linkStyle 10 stroke:red;
linkStyle 20 stroke:red;

linkStyle 18 stroke:blue;
linkStyle 19 stroke:blue;

```

### Dependencies

This is a description of how Smithy Dafny
handles dependencies.

In this example there are 2 packages A and B.
Both are smithy-dafny projects.
B depends on A.

```mermaid
---
title: How Smithy Dafny handles dependencies
---
graph LR

subgraph Legend
  direction LR
  start1[ ] --->|Depends on| stop1[ ]
  style start1 height:0px;
  style stop1 height:0px;
  start2[ ] ===>|Dafny translation to native code| stop2[ ]
  style start2 height:0px;
  style stop2 height:0px;
  start3[ ] -..->|smithy-dafny codegen| stop3[ ]
  style start3 height:0px;
  style stop3 height:0px;
  start4[ ] --->|Testing| stop4[ ]
  style start4 height:0px;
  style stop4 height:0px;
end
linkStyle 1 stroke:blue;
linkStyle 3 stroke:red;

subgraph Smithy
  AModel["Model for A"]
  BModel["Model for B"]

  BModel --> AModel
end

subgraph Dafny
  subgraph A["Package for A"]
    ATypes["Dafny Types for A"]
    AInterface["Dafny Interface for A"]
    AImplementation["Dafny implementation of A"]

    AImplementation --> AInterface
    ATypes --> AInterface
    ATypes --> AImplementation

    AModel -.-> ATypes
    AModel -.-> AInterface
    BModel -.-> ATypes
  end

  B["Package for B"]
  B --> ATypes
  BModel -.-> B

end

subgraph Net[".Net"]
  subgraph NetA["A<sub>.net</sub>"]
    NetAFromDafny
    NetATypes
    NetAInterface
    NetATypeConversion["To/From Dafny"]

    NetATypeConversion --> NetAInterface
    NetAFromDafny --> NetAInterface
    NetATypes --> NetAInterface
    AModel -.-> NetATypes
    AModel -.-> NetAInterface
    AModel -.-> NetATypeConversion
    A ==> NetAFromDafny

    linkStyle 19 stroke:blue;

    ATypes ~~~ NetAInterface
  end

  NetB["B<sub>.net</sub>"]
  B ==> NetB
  linkStyle 21 stroke:blue;

  NetB --> NetAFromDafny
  BModel -.-> NetB

end
```

### Wrapped AWS Services

This diagram is about how
smithy-dafny can wrap an existing
application using a smithy model.
This has been specialized
to handle AWS services.

An example would be how the AWS Encryption SDK
uses the AWS KMS SDK.
Since there does not exist a Dafny AWS SDK
but there does exist native versions
we can wrap the native versions in an extern.

The example uses AWS KMS to help make things clear,
but it could be any service.

```mermaid
---
title: How Smithy Dafny imports a native implementation of a Smithy model to Dafny
---
graph LR

subgraph Legend
  direction LR
  start1[ ] --->|Depends on| stop1[ ]
  style start1 height:0px;
  style stop1 height:0px;
  start2[ ] ===>|Dafny translation to native code| stop2[ ]
  style start2 height:0px;
  style stop2 height:0px;
  start3[ ] -..->|smithy-dafny codegen| stop3[ ]
  style start3 height:0px;
  style stop3 height:0px;
  start4[ ] --->|Testing| stop4[ ]
  style start4 height:0px;
  style stop4 height:0px;
end
linkStyle 1 stroke:blue;
linkStyle 3 stroke:red;

subgraph Smithy
  AModel["Model for KMS"]
end

subgraph Dafny
  subgraph A["KMS<sub>Dafny</sub>"]
    ATypes["Dafny Types for KMS"]
    AInterface["Dafny Interface for KMS"]
    AExtern["Dafny Extern construct Native KMS"]
    AImplementation["Dafny implementation of KMS"]

    AImplementation --> AInterface
    ATypes --> AImplementation
    AExtern --> AImplementation
    ATypes --> AInterface
    ATypes --> AExtern

    AModel -.-> ATypes
    AModel -.-> AInterface
  end

  subgraph ATests["Tests for KMS"]
    AIntegrationTests["Integration Tests for KMS"]
    AIntegrationTests --> AInterface

    NTest["
      There are only integration tests here.
      This is because we need to test
      that this Dafny interface will return
      well formed output to Dafny callers.

      There MAY be a need for unit tests,
      but in that case I assert
      that probably you are adding too much logic.
      The whole reason this exists
      is to get the native Smithy implementation into Dafny.
      More generic externs are handled differently.
    "]
  end
end

subgraph Net[".Net"]
  subgraph NativeNetA["NativeKMS<sub>.net</sub>"]
    NativeNetATypes[Native KMS SDK types]
    NativeNetAInterface[Native KMS SDK interface]
    NativeNetAImplementation[Native KMS SDK]

    NativeNetAImplementation --> NativeNetAInterface
    NativeNetATypes --> NativeNetAImplementation
    NativeNetATypes --> NativeNetAInterface

    AModel -.-> NativeNetATypes
    AModel -.-> NativeNetAInterface
  end

  subgraph NetA["KMS<sub>.net</sub>"]
    NetAFromDafny[Translated Dafny ]
    NetAExtern[Net Extern to return KMS SKD]

    A ==> NetAFromDafny
    linkStyle 17 stroke:blue;
    NetAExtern --> NetAFromDafny
    NetAExtern --> AExtern
    NativeNetAInterface --> NetAExtern

    NNetA["
      There is no interface here.
      This is because this exists for Dafny.
      Any caller other than Dafny
      would prefer to use NativeA.

      There MAY need to be something
      to facilitate passing into Dafny
      an arbitrary NativeA interface.
    "]
  end

  NetATests

  ATests ==> NetATests
  linkStyle 21 stroke:blue;
  NetATests --> NetAFromDafny
end

```

### Extern Library Development

Dafny also allows you to use `extern`
to link to external code.
Linking directly to external code
is complicated.
For the same reason that `smithy-dafny`
exists such types and interfaces
are not fully interoperable.

This is why wrapping the needed external code
inside a library exists.

For this example we will again
pull from the ESDK dependencies.
The Cryptographic Primitives exposes primitive functions
that are externs in each native runtime.

```mermaid
---
title: How Smithy Dafny wraps generic externs to Dafny
---
graph LR

subgraph Legend
  direction LR
  start1[ ] --->|Depends on| stop1[ ]
  style start1 height:0px;
  style stop1 height:0px;
  start2[ ] ===>|Dafny translation to native code| stop2[ ]
  style start2 height:0px;
  style stop2 height:0px;
  start3[ ] -..->|smithy-dafny codegen| stop3[ ]
  style start3 height:0px;
  style stop3 height:0px;
  start4[ ] --->|Testing| stop4[ ]
  style start4 height:0px;
  style stop4 height:0px;
end
linkStyle 1 stroke:blue;
linkStyle 3 stroke:red;


subgraph Smithy
  PrimitiveModel["Model for Cryptographic Primitives"]
end

subgraph Dafny
  direction LR
  subgraph Primitives["Cryptographic Primitives"]
    PrimitiveTypes["Dafny Types for Primitives"]
    PrimitiveInterface["Dafny Interface for Primitives"]
    PrimitiveImplementation["Dafny implementation of Primitives"]

    Encrypt["Dafny Extern to Encrypt"]
    Decrypt["Dafny Extern to Decrypt"]

    PrimitiveImplementation --> PrimitiveInterface
    PrimitiveTypes --> PrimitiveImplementation

    Encrypt --> PrimitiveImplementation
    Decrypt --> PrimitiveImplementation

    PrimitiveTypes --> Encrypt
    PrimitiveTypes --> Decrypt

    PrimitiveTypes --> PrimitiveInterface

    PrimitiveModel -.-> PrimitiveTypes
    PrimitiveModel -.-> PrimitiveInterface
  end

  subgraph PrimitivesTests["Tests for Cryptographic Primitives"]
    PrimitiveUnitTests["Unit Tests for Cryptographic Primitives"]

    EncryptTests["Tests for Encrypt"]
    DecryptTests["Tests for Decrypt"]

    PrimitiveUnitTests --> PrimitiveImplementation
    EncryptTests --> Encrypt
    DecryptTests --> Decrypt

    NTest["
      There are no integration tests here.
      This is because we need to test
      that the externs are consistent
      and well formed across runtimes.

      There MAY be a need for integration tests,
      but in that case I assert
      that probably you are adding too much logic.
      The whole reason this exists
      is to get the extern into Dafny.
    "]
  end
end

subgraph Net[".Net"]
  direction LR
  subgraph NetPrimitives["Primitives<sub>.net</sub>"]
    NetPrimitivesFromDafny

    NetPrimitiveTypes
    NetPrimitiveInterface
    NetPrimitiveTypeConversion["To/From Dafny"]

    NetEncrypt
    NetDecrypt

    NetPrimitiveTypeConversion --> NetPrimitiveInterface
    NetPrimitivesFromDafny --> NetPrimitiveInterface
    NetPrimitiveTypes --> NetPrimitiveInterface
    NetPrimitiveTypes --> NetPrimitiveTypeConversion

    PrimitiveModel -.-> NetPrimitiveTypes
    PrimitiveModel -.-> NetPrimitiveInterface
    PrimitiveModel -.-> NetPrimitiveTypeConversion

    Primitives ==> NetPrimitivesFromDafny
    linkStyle 23 stroke:blue;

    NetEncrypt --> NetPrimitivesFromDafny
    NetDecrypt --> NetPrimitivesFromDafny

    NetEncrypt --> Encrypt
    NetDecrypt --> Decrypt

    NNetPrimitives["
      There is a native interface!
      It may be that customers
      would want to use this package.
      It would provide a consistent interface
      for these underlying operations across runtimes.

      This kind of thing is especially useful in JS.
    "]
  end

  NetPrimitivesTests

  PrimitivesTests ==> NetPrimitivesTests
  linkStyle 28 stroke:blue;
  NetPrimitivesTests --> NetPrimitivesFromDafny
  NetPrimitivesTests --> NetEncrypt
  NetPrimitivesTests --> NetDecrypt
end

subgraph Java["Java"]
  direction LR
  subgraph JavaPrimitives["Primitives<sub>Java</sub>"]
    JavaPrimitivesFromDafny

    JavaPrimitiveTypes
    JavaPrimitiveInterface
    JavaPrimitiveTypeConversion["To/From Dafny"]

    JavaEncrypt
    JavaDecrypt

    JavaPrimitiveTypeConversion --> JavaPrimitiveInterface
    JavaPrimitivesFromDafny --> JavaPrimitiveInterface
    JavaPrimitiveTypes --> JavaPrimitiveInterface
    JavaPrimitiveTypes --> JavaPrimitiveTypeConversion

    PrimitiveModel -.-> JavaPrimitiveTypes
    PrimitiveModel -.-> JavaPrimitiveInterface
    PrimitiveModel -.-> JavaPrimitiveTypeConversion

    Primitives ==> JavaPrimitivesFromDafny
    linkStyle 39 stroke:blue;

    JavaEncrypt --> JavaPrimitivesFromDafny
    JavaDecrypt --> JavaPrimitivesFromDafny

    JavaEncrypt --> Encrypt
    JavaDecrypt --> Decrypt
  end

  JavaPrimitivesTests

  PrimitivesTests ==> JavaPrimitivesTests
  linkStyle 44 stroke:blue;
  JavaPrimitivesTests --> JavaPrimitivesFromDafny
  JavaPrimitivesTests --> JavaEncrypt
  JavaPrimitivesTests --> JavaDecrypt
end

%% Formatting
Dafny ~~~ Net ~~~ Java
Encrypt ~~~ Decrypt


```

### Testing/Verification

Coordinating all these types across different runtimes
is a lot of complexity.
It is important to be able to test and reason about this.
This diagram shows how the project relate and compile
to alow for tests in Dafny to exercise
all the type conversions and elements of polymorph.

```mermaid
---
title: How we verify Polymorph across runtimes
---
graph TD

subgraph Legend
  direction LR
  start1[ ] --->|Depends on| stop1[ ]
  style start1 height:0px;
  style stop1 height:0px;
  start2[ ] ===>|Dafny translation to native code| stop2[ ]
  style start2 height:0px;
  style stop2 height:0px;
  start3[ ] -..->|smithy-dafny codegen| stop3[ ]
  style start3 height:0px;
  style stop3 height:0px;
  start4[ ] --->|Testing| stop4[ ]
  style start4 height:0px;
  style stop4 height:0px;
end
linkStyle 1 stroke:blue;
linkStyle 3 stroke:red;

subgraph Smithy
  Model["A model that uses Polymorph features under test."]
end

NTest["
 This is applying Polymorph reflexively.
 We are building a Polymorph library,
 and then importing the native version
 of that library into Dafny.
 This lets us write tests about Polymorph in Dafny.

 This makes the Dafny side invariant for every runtime!
"]

Smithy ~~~ Legend
Legend ~~~ NTest

subgraph Dafny
  subgraph TestPackage
    TestPackageInterface
    TestPackageTypes
    TestPackageImplementation
  end

  subgraph ProxyForTest["Package outside TestPackage's Polymorph glue"]
    ProxyForTestTypes
    ProxyForTestInterface
    ProxyForTestExtern
    ProxyForTestImplementation
  end

  subgraph PolymorphTests["Tests for Polymorph"]
    PolymorphTestsIntegrationTests
  end
end

subgraph Net[".Net"]
  NetPolymorphTests

  subgraph NetTestPackage["TestPackage<sub>.net</sub>"]
    NetTestPackageInterface
    NetTestPackageTypes
    NetTestPackageTypeConversion["To/From Dafny"]
    NetTestPackageFromDafny
  end

  subgraph NetProxyForTest["ProxyForTest<sub>.net</sub>"]
    NetProxyForTestFromDafny
    NetProxyForTestExtern
  end
end

TestPackageImplementation --> TestPackageInterface
TestPackageTypes --> TestPackageImplementation
TestPackageTypes --> TestPackageInterface
ProxyForTestImplementation --> ProxyForTestInterface
ProxyForTestTypes --> ProxyForTestImplementation
ProxyForTestExtern --> ProxyForTestImplementation
ProxyForTestTypes --> ProxyForTestInterface
ProxyForTestTypes --> ProxyForTestExtern
NetTestPackageFromDafny --> NetTestPackageInterface
NetTestPackageTypeConversion --> NetTestPackageInterface
NetTestPackageTypes --> NetTestPackageFromDafny
NetTestPackageTypes --> NetTestPackageInterface
NetTestPackageTypes --> NetTestPackageTypeConversion
NetProxyForTestExtern --> NetProxyForTestFromDafny
ProxyForTestExtern --> NetProxyForTestExtern
NetTestPackageInterface --> NetProxyForTestExtern

Model -.-> TestPackageInterface
Model -.-> TestPackageTypes
Model -.-> ProxyForTestTypes
Model -.-> ProxyForTestInterface
Model -.-> NetTestPackageTypes
Model -.-> NetTestPackageInterface
Model -.-> NetTestPackageTypeConversion

TestPackage ==> NetTestPackageFromDafny
ProxyForTest ==> NetProxyForTestFromDafny
PolymorphTests ==> NetPolymorphTests

linkStyle 29,30,31 stroke: blue

```

This diagram takes the components above,
and walks through the testing flow.
Note how the tests start and end in Dafny.

```mermaid
---
title: Flow of test information
---
graph TD


subgraph Dafny
  subgraph TestPackage
    TestPackageInterface
    TestPackageTypes
    TestPackageImplementation
  end

  subgraph ProxyForTest["Package outside TestPackage's Polymorph glue"]
    ProxyForTestTypes
    ProxyForTestInterface
    ProxyForTestExtern
    ProxyForTestImplementation
  end

  subgraph PolymorphTests["Tests for Polymorph"]
    PolymorphTestsIntegrationTests
  end
end

subgraph Net[".Net"]
  subgraph NetTestPackage["TestPackage<sub>.net</sub>"]
    NetTestPackageInterface
    NetTestPackageTypes
    NetTestPackageTypeConversion["To/From Dafny"]
    NetTestPackageFromDafny
  end


  subgraph NetProxyForTest["ProxyForTest<sub>.net</sub>"]
    NetProxyForTestFromDafny
    NetProxyForTestExtern
  end
  NetPolymorphTests
end

PolymorphTestsIntegrationTests --> NetPolymorphTests
NetPolymorphTests --> NetProxyForTestFromDafny
NetProxyForTestFromDafny --> ProxyForTestInterface
ProxyForTestInterface --> ProxyForTestImplementation
ProxyForTestImplementation --> ProxyForTestExtern
ProxyForTestExtern --> NetProxyForTestExtern
NetProxyForTestExtern --> NetTestPackageInterface
NetTestPackageInterface --> NetTestPackageTypeConversion
NetTestPackageTypeConversion --> NetTestPackageFromDafny
NetTestPackageFromDafny --> TestPackageInterface
TestPackageInterface --> TestPackageImplementation

```
