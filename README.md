# AWS Cryptographic Material Providers Library

The AWS Cryptographic Material Providers Library abstracts lower level cryptographic materials management of encryption and decryption materials.
It uses cryptographic best practices to protect the data keys that protect your data.
The data key is protected with a key encryption key called a *wrapping key*.
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

### Optional Prerequisites

#### AWS Integration
You don't need an Amazon Web Services (AWS) account to use the AWS Cryptographic Material Providers Library,
but some APIs require an AWS account, an AWS KMS key, or an Amazon DynamoDB Table. 
If you are using the AWS Cryptographic Material Providers Library for Java you will need the AWS SDK for Java V2.
If you are using the AWS Cryptographic Material Providers Library for .NET you will need the AWS SDK for .NET V3.

**NOTE**: The `KmsAsyncClient` and `DynamoDBAsyncClient` are not supported, only the synchronous clients.

* **To create an AWS account**, go to [Sign In or Create an AWS Account](https://portal.aws.amazon.com/gp/aws/developer/registration/index.html) and then choose **I am a new user.** Follow the instructions to create an AWS account.

* **To create a symmetric encryption KMS key in AWS KMS**, see [Creating Keys](https://docs.aws.amazon.com/kms/latest/developerguide/create-keys.html).

* **To download and install the AWS SDK for Java 2.x**, see [Installing the AWS SDK for Java 2.x](https://docs.aws.amazon.com/sdk-for-java/v2/developer-guide/getting-started.html).
* **To download and install the AWS SDK for .Net 3.x** see [Installing the AWS SDK for .Net v3](https://docs.aws.amazon.com/sdk-for-net/v3/developer-guide/welcome.html)

## FAQ

See the [Frequently Asked Questions](https://docs.aws.amazon.com/encryption-sdk/latest/developer-guide/faq.html) page in the official documentation.
