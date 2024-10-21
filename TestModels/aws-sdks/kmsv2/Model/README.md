This is the [KMS smithy model](https://github.com/aws/aws-models/blob/a7e23cbfde9a5fc0b52c78ff969d72bfb8d8b6f8/kms/smithy/model.json),
but with a couple adjustments:

- The `ListRetirableGrants` operation is removed from the model, and from `com.amazon.kms#KeyManagementService`.
  - This is because its output shape is represented inconsistently in the .NET AWS SDK.
