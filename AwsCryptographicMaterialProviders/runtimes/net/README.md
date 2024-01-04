# AWS Cryptographic Material Providers Library for .NET

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

The AWS Cryptographic Material Providers Library for .NET provides methods for encrypting and decrypting cryptographic materials used in higher level client side encryption libraries.

## Security

If you discover a potential security issue in this project
we ask that you notify AWS/Amazon Security via our
[vulnerability reporting page](http://aws.amazon.com/security/vulnerability-reporting/).
Please **do not** create a public GitHub issue.

## Getting Started

### Required Prerequisites

To use the AWS Cryptographic Material Providers Library for .NET you must have:

- **A .NET Framework 6.0 development environment**

  If you do not have it installed, you can find installation instructions [here](https://dotnet.microsoft.com/en-us/download/dotnet/6.0).

- **Bouncy Castle**

  The AWS Cryptographic Material Providers Library for .NET uses Bouncy Castle for the underlying cryptography and to serialize and deserialize cryptographic objects.

  If you do not have Bouncy Castle, go to https://www.bouncycastle.org/csharp/ to learn more.
  You can also download it from NuGet

  ```
    <PackageReference Include="BouncyCastle.Cryptography" Version="2.2.1" />
  ```

### Optional Prerequisites

#### AWS Integration

You don't need an Amazon Web Services (AWS) account to use the AWS Cryptographic Material Providers Library,
but some APIs require an AWS account, an AWS KMS key, or an AWS DynamoDB Table.
However, all APIs require the AWS SDK for .NET V3.

Note that `Async AmazonKeyManagementServiceClient` and `Async DynamoDBAsyncClient` methods are not supported, only the synchronous methods.

- **To create an AWS account**, go to [Sign In or Create an AWS Account](https://portal.aws.amazon.com/gp/aws/developer/registration/index.html) and then choose **I am a new user.** Follow the instructions to create an AWS account.

- **To create a KMS key in AWS KMS**, see [Creating Keys](https://docs.aws.amazon.com/kms/latest/developerguide/create-keys.html).

- **To download and install the AWS SDK for .NET 3.x**, see [Installing the AWS SDK for .NET 3.x](https://docs.aws.amazon.com/sdk-for-net/v3/developer-guide/net-dg-install-assemblies.html).

### Download the AWS Cryptographic Material Providers Library for .NET

The AWS Cryptographic Material Providers Library for .NET is available on NuGet and can be referenced
from an existing .csproj.

Using the dotnet CLI:

```shell
dotnet add <your-project-name>.csproj package AWS.Cryptography.MaterialProviders
```

Alternatively, you may directly modify the `.csproj` and add the
AWS Cryptographic Material Providers Library to `PackageReference` `ItemGroup`:

```xml
<PackageReference Include="AWS.Cryptography.MaterialProviders" />
```

The AWS Cryptographic Material Providers Library targets:

- [.NET Framework](https://docs.microsoft.com/en-us/dotnet/framework/) 4.8.
- [.NET](https://learn.microsoft.com/en-us/dotnet/core/whats-new/dotnet-6) 6.0.
- [.NET Standard](https://learn.microsoft.com/en-us/dotnet/standard/net-standard?tabs=net-standard-2-0) 2.0.

### Additional setup for macOS only

If you are using macOS then you must install OpenSSL 1.1,
and the OpenSSL 1.1 `lib` directory must be on the dynamic linker path at runtime.
Also, if using an M1-based Mac, you must install OpenSSL and the .NET SDK for x86-64.
Please refer to [this wiki](https://github.com/aws/aws-encryption-sdk-dafny/wiki/Using-the-AWS-Encryption-SDK-for-.NET-on-macOS) for detailed instructions.

## License

This library is licensed under the Apache 2.0 License.
