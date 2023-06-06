# AWS Cryptographic Material Providers Library for Java

The AWS Cryptographic Material Providers Library abstracts lower level cryptographic materials management of encryption and decryption materials.
It uses cryptographic best practices to protect the data keys that protect your data.
The data key is protected with a key encryption key called a *wrapping key* or *master key*.
The encryption method returns the data key and one or more encrypted data keys.
Supported libraries use this information to perform envelope encryption.
The data key is used to protect your data,
and the encrypted data keys are stored alongside your data
so you don't need to keep track of the data keys separately.
You can use AWS KMS keys in [AWS Key Management Service](https://aws.amazon.com/kms/)(AWS KMS) as wrapping keys.
The AWS Cryptographic Material Providers Library
also provides APIs to define and use wrapping keys from other key providers. 

The AWS Cryptographic Material Providers Library for Java provides methods for encrypting and decrypting cryptographic materials used in higher level client side encryption libraries. 

[Security issue notifications](./CONTRIBUTING.md#security-issue-notifications)

## Security
If you discover a potential security issue in this project
we ask that you notify AWS/Amazon Security via our
[vulnerability reporting page](http://aws.amazon.com/security/vulnerability-reporting/).
Please **do not** create a public GitHub issue.

## Getting Started

### Required Prerequisites
To use the AWS Cryptographic Material Providers Library for Java you must have:

* **A Java 8 or newer development environment**

  If you do not have one, we recommend [Amazon Corretto](https://aws.amazon.com/corretto/).

  **Note:** If you use the Oracle JDK, you must also download and install the [Java Cryptography Extension (JCE) Unlimited Strength Jurisdiction Policy Files](http://www.oracle.com/technetwork/java/javase/downloads/jce8-download-2133166.html).

* **Bouncy Castle** or **Bouncy Castle FIPS**

  The AWS Cryptographic Material Providers Library for Java uses Bouncy Castle to serialize and deserialize cryptographic objects.
  It does not explicitly use Bouncy Castle (or any other [JCA Provider](https://docs.oracle.com/javase/8/docs/api/java/security/Provider.html)) for the underlying cryptography.
  Instead, it uses the platform default, which you can configure or override as documented in the
  [Java Cryptography Architecture (JCA) Reference Guide](https://docs.oracle.com/javase/9/security/java-cryptography-architecture-jca-reference-guide.htm#JSSEC-GUID-2BCFDD85-D533-4E6C-8CE9-29990DEB0190).

  If you do not have Bouncy Castle, go to https://bouncycastle.org/latest_releases.html, then download the provider file that corresponds to your JDK.
  Or, you can pick it up from Maven (groupId: `org.bouncycastle`, artifactId: `bcprov-ext-jdk18on`).

### Optional Prerequisites

#### AWS Integration
You don't need an Amazon Web Services (AWS) account to use the AWS Cryptographic Material Providers Library, but some APIs require an AWS account, an AWS KMS key, an AWS DynamoDB Table, and the AWS SDK for Java V2. Note that the `KmsAsyncClient` and `DynamoDBAsyncClient` are not supported, only the synchronous clients.

* **To create an AWS account**, go to [Sign In or Create an AWS Account](https://portal.aws.amazon.com/gp/aws/developer/registration/index.html) and then choose **I am a new user.** Follow the instructions to create an AWS account.

* **To create a symmetric encryption KMS key in AWS KMS**, see [Creating Keys](https://docs.aws.amazon.com/kms/latest/developerguide/create-keys.html).

* **To download and install the AWS SDK for Java 2.x**, see [Installing the AWS SDK for Java 2.x](https://docs.aws.amazon.com/sdk-for-java/v2/developer-guide/getting-started.html).

#### Amazon Corretto Crypto Provider
Many users find that the Amazon Corretto Crypto Provider (ACCP) significantly improves the performance of the AWS Encryption SDK.
For help installing and using ACCP, see the [amazon-corretto-crypto-provider repository](https://github.com/corretto/amazon-corretto-crypto-provider).

### Download the AWS Cryptographic Material Providers Library for Java
You can get the latest release from Maven or Gradle:

#### Maven:

```xml
<dependency>
  <groupId>software.amazon.cryptography</groupId>
  <artifactId>aws-cryptographic-material-providers</artifactId>
  <version>1.0.0</version>
</dependency>
```

#### Gradle:
```
dependencies {
    implementation("software.amazon.cryptography:aws-cryptographic-material-providers:1.0.0")
}
```

## Public API

Our [versioning policy](./VERSIONING.rst) applies to all public and protected classes/methods/fields
in the  `software.amazon.cryptography.materialproviders` package unless otherwise documented.

The `software.amazon.cryptography.materialproviders.internaldafny` package is not included in this public API.

## FAQ

See the [Frequently Asked Questions](https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/faq.html) page in the official documentation.
