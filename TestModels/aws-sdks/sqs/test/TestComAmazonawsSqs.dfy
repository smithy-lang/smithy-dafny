// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Something like this should work once we implement the
// "dafny-client-codegen" Smithy build plugin and
// configure it in smithy-build.json.
// Note the lack of any manually-written code in the project!

include "../src/Index.dfy"

module TestComAmazonawsSqs {
  import Com.Amazonaws.Sqs
  import opened StandardLibrary.UInt
  import opened Wrappers

  // TODO: Enable {:test} once the GitHub-CI-PolymorphTestModels-Role-us-west-2 role
  // has the necessary permissions.
  method BasicSanityTest()
  {
    var client :- expect Sqs.SQSClient();

    var input := Sqs.Types.ListQueuesRequest(
      QueueNamePrefix := None,
      NextToken := None,
      MaxResults := None
    );
    var ret: Sqs.Types.ListQueuesResult :- expect client.ListQueues(input);

    var ListQueuesResult(NextToken, QueueUrls) := ret;

    expect QueueUrls.Some?;
    expect |QueueUrls.value| == 1;
  }
}
