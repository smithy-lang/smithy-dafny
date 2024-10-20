// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../Model/ComAmazonawsSqsextendedTypes.dfy"
module AmazonSQSExtendedImpl refines AbstractComAmazonawsSqsextendedOperations {
  datatype Config = Config(
    nameonly sqsClient : ComAmazonawsSqsTypes.ISQSClient
  )
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {
    config.sqsClient.ValidState()
  }
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {
    config.sqsClient.Modifies
  }
  predicate HandleMessagesEnsuresPublicly(input: HandleMessagesInput , output: Result<(), Error>)
  {true}



  method HandleMessages ( config: InternalConfig , input: HandleMessagesInput )
    returns (output: Result<(), Error>)

  {
    var queueUrl := input.receiveRequest.QueueUrl;

    var maybeMessagesResult := config.sqsClient.ReceiveMessage(input.receiveRequest);
    var messagesResult :- maybeMessagesResult.MapFailure(e => ComAmazonawsSqs(e));
    // TODO: Handle error better
    expect messagesResult.Messages.Some?;
    var messages :- expect messagesResult.Messages;

    for i := 0 to |messages| {
      var message := messages[i];
      // TODO: Handle error better
      var receiptHandle :- expect message.ReceiptHandle;

      var messageResult := input.handler.HandleMessage(HandleMessageInput(message := message));

      if messageResult.Success? {
        var deleteResult := config.sqsClient.DeleteMessage(ComAmazonawsSqsTypes.DeleteMessageRequest(
          QueueUrl := queueUrl,
          ReceiptHandle := receiptHandle
        ));
      } else {
        // TODO: Handle retryable errors
        var deleteResult := config.sqsClient.ChangeMessageVisibility(ComAmazonawsSqsTypes.ChangeMessageVisibilityRequest(
          QueueUrl := queueUrl,
          ReceiptHandle := receiptHandle,
          VisibilityTimeout := 0
        ));
      }
    }

    output := Success(());
  }
}
