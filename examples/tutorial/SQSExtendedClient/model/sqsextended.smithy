$version: "2"

namespace com.amazonaws.sqsextended

use com.amazonaws.sqs#Message

@aws.polymorph#localService(
  sdkId: "SQSExtended",
  config: SQSExtendedClientConfig,
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
  errors: [],
}
structure SQSExtendedClientConfig {
  @required
  sqsClient: SQSClientReference
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

}


operation HandleMessages {
  input := {
    @required
    receiveRequest: com.amazonaws.sqs#ReceiveMessageRequest,

    @required
    handler: MessageHandlerReference
  }
}