$version: "2"

namespace polymorph.tutorial

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

