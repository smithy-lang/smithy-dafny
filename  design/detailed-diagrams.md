
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
packages its dependencies
we can see that having duplicate symbols
for the `Crypto` library is problematic.

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

    AModel -.->|CodeGen| ATypes
    AModel -.->|CodeGen| AInterface
  end

  subgraph ATests["Tests for A"]
    AUnitTests["Unit Tests for A"]
    AIntegrationTests["Integration Tests for A"]

    AUnitTests --> |Testing| AImplementation
    AIntegrationTests -->|Testing| AInterface
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
    AModel -.->|CodeGen| NetATypes
    AModel -.->|CodeGen| NetAInterface
    AModel -.->|CodeGen| NetATypeConversion
    A ==>|Dafny Compilation| NetAFromDafny
  end

  NetATests

  ATests ==>|Dafny Compilation| NetATests
  NetATests -->|Testing| NetAFromDafny
end
```

### Dependencies

This is a description of how Smithy Dafny
handles dependencies.

```mermaid
---
title: How Smithy Dafny handles dependencies
---
graph LR

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

    AModel -.->|CodeGen| ATypes
    AModel -.->|CodeGen| AInterface
    BModel -.->|CodeGen| ATypes
  end

  B["Package for B"]
  B --> ATypes
  BModel -.->|CodeGen| B

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
    AModel -.->|CodeGen| NetATypes
    AModel -.->|CodeGen| NetAInterface
    AModel -.->|CodeGen| NetATypeConversion
    A ==>|Dafny Compilation| NetAFromDafny

    ATypes ~~~ NetAInterface
  end

  NetB["B<sub>.net</sub>"]
  B ==>|Dafny Compilation| NetB

  NetB --> NetAFromDafny
  BModel -.->|CodeGen| NetB

end
```

### Wrapped AWS Services

This diagram is about how
smithy-dafny can wrap an existing
application using a smithy model.
This has been specialized
to handle AWS services.


```mermaid
---
title: How Smithy Dafny imports a native implementation of a Smithy model to Dafny
---
graph LR

subgraph Smithy
  AModel["Model for A"]
end

subgraph Dafny
  subgraph A["Package for A"]
    ATypes["Dafny Types for A"]
    AInterface["Dafny Interface for A"]
    AExtern["Dafny Extern to NativeA"]
    AImplementation["Dafny implementation of A"]

    AImplementation --> AInterface
    ATypes --> AImplementation
    AExtern --> AImplementation
    ATypes --> AInterface
    ATypes --> AExtern

    AModel -.->|CodeGen| ATypes
    AModel -.->|CodeGen| AInterface
  end

  subgraph ATests["Tests for A"]
    AIntegrationTests["Integration Tests for A."]
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
  subgraph NativeNetA["NativeA<sub>.net</sub>"]
    NativeNetATypes
    NativeNetAInterface
    NativeNetAImplementation

    NativeNetAImplementation --> NativeNetAInterface
    NativeNetATypes --> NativeNetAImplementation
    NativeNetATypes --> NativeNetAInterface

    AModel -.->|CodeGen| NativeNetATypes
    AModel -.->|CodeGen| NativeNetAInterface
  end

  subgraph NetA["A<sub>.net</sub>"]
    NetAFromDafny
    NetAExtern

    A ==>|Dafny Compilation| NetAFromDafny
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

  ATests ==>|Dafny Compilation| NetATests
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


```mermaid
---
title: How Smithy Dafny wraps generic externs to Dafny
---
graph LR

subgraph Smithy
  AModel["Model for A"]
end

subgraph Dafny
  subgraph A["Package for A"]
    ATypes["Dafny Types for A"]
    AInterface["Dafny Interface for A"]
    AImplementation["Dafny implementation of A"]

    AExtern1["Dafny Extern to NativeA"]
    AExtern2["Dafny Extern to NativeA"]
    AExtern3["Dafny Extern to NativeA"]
    AExtern4["Dafny Extern to NativeA"]

    AImplementation --> AInterface
    ATypes --> AImplementation

    AExtern4 --> AImplementation
    AExtern1 --> AImplementation
    AExtern2 --> AImplementation
    AExtern3 --> AImplementation

    ATypes --> AExtern1
    ATypes --> AExtern2
    ATypes --> AExtern3
    ATypes --> AExtern4

    ATypes --> AInterface

    AModel -.->|Polymorph| ATypes
    AModel -.->|Polymorph| AInterface
  end

  subgraph ATests["Tests for A"]
    AUnitTests["Unit Tests for A"]

    AExtern1Tests["Tests for Extern1"]
    AExtern2Tests["Tests for Extern2"]
    AExtern3Tests["Tests for Extern3"]
    AExtern4Tests["Tests for Extern4"]

    AUnitTests --> AImplementation
    AExtern1Tests --> AExtern1
    AExtern2Tests --> AExtern2
    AExtern3Tests --> AExtern3
    AExtern4Tests --> AExtern4

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
  subgraph NetA["A<sub>.net</sub>"]
    NetAFromDafny

    NetATypes
    NetAInterface
    NetATypeConversion["To/From Dafny"]

    NetAExtern1
    NetAExtern2
    NetAExtern3
    NetAExtern4

    NetATypeConversion --> NetAInterface
    NetAFromDafny --> NetAInterface
    NetATypes --> NetAInterface
    NetATypes --> NetATypeConversion

    AModel -.->|Polymorph| NetATypes
    AModel -.->|Polymorph| NetAInterface
    AModel -.->|Polymorph| NetATypeConversion

    A ==>|Dafny Compilation| NetAFromDafny

    NetAExtern1 --> NetAFromDafny
    NetAExtern2 --> NetAFromDafny
    NetAExtern3 --> NetAFromDafny
    NetAExtern4 --> NetAFromDafny

    NetAExtern1 --> AExtern1
    NetAExtern2 --> AExtern2
    NetAExtern3 --> AExtern3
    NetAExtern4 --> AExtern4

    NNetA["
      There is a native interface!
      It may be that customers
      would want to use this package.
      It would provide a consistent interface
      for these underlying operations across runtimes.

      This kind of thing is especially useful in JS.
    "]
  end

  NetATests

  ATests ==>|Dafny Compilation| NetATests
  NetATests --> NetAFromDafny
  NetATests --> NetAExtern1
  NetATests --> NetAExtern2
  NetATests --> NetAExtern3
  NetATests --> NetAExtern4

end

%% Formatting
Smithy ~~~~~ Dafny

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

Model -.->|Polymorph| TestPackageInterface
Model -.->|Polymorph| TestPackageTypes
Model -.->|Polymorph| ProxyForTestTypes
Model -.->|Polymorph| ProxyForTestInterface
Model -.->|Polymorph| NetTestPackageTypes
Model -.->|Polymorph| NetTestPackageInterface
Model -.->|Polymorph| NetTestPackageTypeConversion

TestPackage ==>|Dafny Compilation| NetTestPackageFromDafny
ProxyForTest ==>|Dafny Compilation| NetProxyForTestFromDafny
PolymorphTests ==>|Dafny Compilation| NetTestPackageInterface

linkStyle 23,24,25 stroke: red
linkStyle 16,17,18,19,20,21,22 stroke: blue

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
