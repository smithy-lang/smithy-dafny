// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module {:options "--function-syntax:4"} SQSExtendedClientImplTest {

    import Com.Amazonaws.SQS
    import ComAmazonawsSqsTypes
    import SQSExtended
    import opened PolymorphTutorialSqsextendedTypes
    import opened Wrappers

    method {:test} TestClient() {
        var sqsClient :- expect SQS.SQSClient();
        var extendedClient :- expect SQSExtended.SQSExtended(
            SQSExtendedClientConfig(sqsClient := sqsClient)
        );

        TestHandleMessages(sqsClient, extendedClient);
    }

    method TestHandleMessages(sqsClient: ComAmazonawsSqsTypes.ISQSClient, extendedClient: SQSExtended.SQSExtendedClient)
        requires sqsClient.ValidState()
        requires extendedClient.ValidState()
        modifies 
            sqsClient.Modifies, 
            sqsClient.History,
            extendedClient.Modifies
     {
        // Create test queue
        var createQueueResponse :- expect sqsClient.CreateQueue(ComAmazonawsSqsTypes.CreateQueueRequest(
            QueueName := "PolymorphExtendedSQSTest"
        ));
        var queueUrl :- expect createQueueResponse.QueueUrl;
        
        // Send a message
        var sendMessageResponse :- expect sqsClient.SendMessage(ComAmazonawsSqsTypes.SendMessageRequest(
            QueueUrl := queueUrl,
            MessageBody := "Hello world!"
        ));

        // Receive and handle the message
        var receiveMessagesRequest := ComAmazonawsSqsTypes.ReceiveMessageRequest(
            QueueUrl := queueUrl,
            WaitTimeSeconds := Some(20)
        );
        var handler := new MyMessageHandler();
        var result :- expect extendedClient.HandleMessages(HandleMessagesInput(
            receiveRequest := receiveMessagesRequest,
            handler := handler
        )); 
    }


    class MyMessageHandler extends IMessageHandler {
        constructor() 
            ensures ValidState()
            ensures fresh(History)
            ensures fresh(Modifies)
        {
            History := new IMessageHandlerCallHistory();
            Modifies := {History};
        }

        ghost predicate ValidState()
            ensures ValidState() ==> History in Modifies 
        {
            History in Modifies 
        }

        ghost predicate HandleMessageEnsuresPublicly(input: HandleMessageInput , output: Result<(), Error>)
        {
            true
        }

        method HandleMessage' ( input: HandleMessageInput )
            returns (output: Result<(), Error>)
            requires
                && ValidState()
            modifies Modifies - {History}
            // Dafny will skip type parameters when generating a default decreases clause.
            decreases Modifies - {History}
            ensures
                && ValidState()
            ensures HandleMessageEnsuresPublicly(input, output)
            ensures unchanged(History)
        {
            print "Got a message: ", input.message.Body;
            return Success(());
        }
    }
}
