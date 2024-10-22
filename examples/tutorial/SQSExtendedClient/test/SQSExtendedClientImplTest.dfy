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

        expect false, "...that you'll write actual tests using the client here :)";
        // TestSomeOperation1(client);
        // TestSomeOperation2(client);
        // ...
    }

    method TestHandleMessages(client: SQSExtended.SQSExtendedClient)
        requires client.ValidState()
        modifies client.Modifies
     {
        var receiveMessagesRequest := ComAmazonawsSqsTypes.ReceiveMessageRequest(
            QueueUrl := "foo"
        );
        var handler := new MyMessageHandler();
        var result := client.HandleMessages(PolymorphTutorialSqsextendedTypes.HandleMessagesInput(
            receiveRequest := receiveMessagesRequest,
            handler := handler
        )); 
    }


    class MyMessageHandler extends PolymorphTutorialSqsextendedTypes.IMessageHandler {
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
