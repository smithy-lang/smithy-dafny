$version: "2"
namespace example.sqsextendedclient

@aws.polymorph#localService(
  sdkId: "SQSExtendedClient",
  config: SQSExtendedClientConfig,
)
service SQSExtendedClient {
  version: "2021-11-01",
  resources: [ AWSCredentialsProvider ],
  operations: [
    CreateDefaultCredentialsProvider,
    CreateQueue,
    SendMessageThroughS3,
    ReceiveMessageThroughS3
  ],
  errors: [],
}
structure SQSExtendedClientConfig {}

///
/// The AWSCredentialsProvider resource shape.
/// Essentially a callback for obtaining credentials.
///
// Something like this is likely reusable across many different Polymorph libraries
// that depend on AWS clients.
resource AWSCredentialsProvider {
  operations: [
    GetCredentials
  ]
}

// Creates an opaque shape used to reference an AWSCredentialsProvider.
// Tagging an empty structure is just a way to fit into the Smithy type system:
// this trait changes the nature of the shape just as @enum does to String shapes.
@aws.polymorph#reference(resource: AWSCredentialsProvider)
structure AWSCredentialsProviderReference {}

operation GetCredentials {
  output: AWSCredentials
}

structure AWSCredentials {
  username: String
  @sensitive
  password: String
}

operation CreateDefaultCredentialsProvider {
  output := {
    credentialsProvider: AWSCredentialsProvider
  }
}

operation CreateQueue {
  input := {
    credentialsProvider: AWSCredentialsProvider
    queueName: String
  }
  output := {
    queueUrl: String
  }
}

operation SendMessageThroughS3 {
  input := {
    credentialsProvider: AWSCredentialsProviderReference
    queueUrl: String
    message: String
  }
}

operation ReceiveMessageThroughS3 {
  input := {
    credentialsProvider: AWSCredentialsProviderReference
    queueUrl: String
  }
  output := {
    message: String
  }
}