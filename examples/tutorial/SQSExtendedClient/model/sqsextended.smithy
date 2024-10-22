$version: "2"

namespace polymorph.tutorial.sqsextended

use com.amazonaws.sqs#Message

@aws.polymorph#localService(
  sdkId: "SQSExtended",
  config: SQSExtendedClientConfig,
  configRequired: true,
  dependencies: [
    com.amazonaws.sqs#AmazonSQS
  ]
)
service AmazonSQSExtended {
  version: "2021-11-01",
  resources: [ MessageHandler ],
  operations: [
    HandleMessages,
  ],
  errors: [SQSExtendedError],
}
structure SQSExtendedClientConfig {
  @required
  sqsClient: SQSClientReference
}
@error("server")
structure SQSExtendedError {
  @required
  message: String
}

@aws.polymorph#reference(service: com.amazonaws.sqs#AmazonSQS)
structure SQSClientReference {}

resource MessageHandler {
  operations: [
    HandleMessage,
  ],
}

@aws.polymorph#reference(resource: MessageHandler)
structure MessageHandlerReference {}

operation HandleMessage {
  input := {
    @required
    message: Message
  }
  errors: [RetryMessageError]
}

@error("client")
structure RetryMessageError {
  @required
  message: String
}

operation HandleMessages {
  input := {
    @required
    receiveRequest: com.amazonaws.sqs#ReceiveMessageRequest,

    @required
    handler: MessageHandlerReference
  }
}