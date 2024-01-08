# AWS Cryptographic Material Providers Library

The AWS Cryptographic Material Providers Library abstracts lower level cryptographic materials management of encryption and decryption materials.
It uses cryptographic best practices to protect the data keys that protect your data.
The data key is protected with a key encryption key called a _wrapping key_.
The encryption method returns the data key and one or more encrypted data keys.
Supported libraries use this information to perform envelope encryption.
The data key is used to protect your data,
and the encrypted data keys are stored alongside your data
so you don't need to keep track of the data keys separately.
You can use AWS KMS keys in [AWS Key Management Service](https://aws.amazon.com/kms/)(AWS KMS) as wrapping keys.
The AWS Cryptographic Material Providers Library
also provides APIs to define and use wrapping keys from other key providers.

The AWS Cryptographic Material Providers Library provides methods for encrypting and decrypting cryptographic materials used in higher level client side encryption libraries.

[Security issue notifications](./CONTRIBUTING.md#security-issue-notifications)

## Security

If you discover a potential security issue in this project
we ask that you notify AWS/Amazon Security via our
[vulnerability reporting page](http://aws.amazon.com/security/vulnerability-reporting/).
Please **do not** create a public GitHub issue.

## Getting Started

### Repository structure

This repository is a top level repository which houses all source code in order to compile this library into
different runtimes.

This library is written in Dafny, a formally verifiable programming language that can be compiled into
different runtimes. This library is currently **ONLY** supported in Java and .NET

### Required Prerequisites

To use the AWS Material Providers Library in Java, you must have:

- **A Java 8 or newer development environment**
  If you do not have one,
  go to [Java SE Downloads](https://www.oracle.com/technetwork/java/javase/downloads/index.html) on the Oracle website,
  then download and install the Java SE Development Kit (JDK).
  Java 8 or higher is required.

  **Note:** If you use the Oracle JDK,
  you must also download and install
  the [Java Cryptography Extension (JCE) Unlimited Strength Jurisdiction Policy Files](http://www.oracle.com/technetwork/java/javase/downloads/jce8-download-2133166.html).

- **Declare a Dependency on AWS Material Providers Library in Java and it's dependencies**
  This library requires the DynamoDB and KMS clients
  from the AWS SDK for Java V2

  - **Via Gradle Kotlin**
    In a Gradle Java Project, add the following to the _dependencies_ section:

  ```kotlin
  implementation("software.amazon.cryptography:aws-cryptographic-material-providers:1.2.0")
  implementation(platform("software.amazon.awssdk:bom:2.19.1"))
  implementation("software.amazon.awssdk:dynamodb")
  implementation("software.amazon.awssdk:kms")
  ```

  - **Via Apache Maven**
    Add the following to your project's `pom.xml`.

  ```xml
  <project>
  ...
  <dependencyManagement>
   <dependencies>
      <dependency>
        <groupId>software.amazon.awssdk</groupId>
        <artifactId>bom</artifactId>
        <version>2.19.1</version>
        <type>pom</type>
        <scope>import</scope>
      </dependency>
   </dependencies>
  </dependencyManagement>
  <dependencies>
    <dependency>
      <groupId>software.amazon.awssdk</groupId>
      <artifactId>dynamodb</artifactId>
    </dependency>
    <dependency>
      <groupId>software.amazon.awssdk</groupId>
      <artifactId>kms</artifactId>
    </dependency>
    <dependency>
      <groupId>software.amazon.cryptography</groupId>
      <artifactId>aws-cryptographic-material-providers</artifactId>
      <version>1.2.0</version>
    </dependency>
  </dependencies>
  ...
  </project>
  ```

### Optional Prerequisites

#### AWS Integration

You don't need an Amazon Web Services (AWS) account to use the AWS Cryptographic Material Providers Library,
but some APIs require an AWS account, an AWS KMS key, or an Amazon DynamoDB Table.
If you are using the AWS Cryptographic Material Providers Library for Java you will need the AWS SDK for Java V2.

**NOTE**: The `KmsAsyncClient` and `DynamoDBAsyncClient` are not supported, only the synchronous clients.

- **To create an AWS account**, go to [Sign In or Create an AWS Account](https://portal.aws.amazon.com/gp/aws/developer/registration/index.html) and then choose **I am a new user.** Follow the instructions to create an AWS account.

- **To create a symmetric encryption KMS key in AWS KMS**, see [Creating Keys](https://docs.aws.amazon.com/kms/latest/developerguide/create-keys.html).

- **To download and install the AWS SDK for Java 2.x**, see [Installing the AWS SDK for Java 2.x](https://docs.aws.amazon.com/sdk-for-java/v2/developer-guide/getting-started.html).

## FAQ

See the [Frequently Asked Questions](https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/faq.html) page in the official documentation.
