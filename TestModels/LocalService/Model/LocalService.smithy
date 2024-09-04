// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
$version: "2"
namespace simple.localService

@aws.polymorph#localService(
  sdkId: "SimpleLocalService",
  config: SimpleLocalServiceConfig,
)
service SimpleLocalService {
  version: "2021-11-01",
  resources: [],
  operations: [HelloWorld, SelfReflection],
  errors: [ SimpleLocalServiceException ],
}

structure SimpleLocalServiceConfig {}

@error("client")
structure SimpleLocalServiceException {
  @required
  message: String,
}

@aws.polymorph#reference(service: SimpleLocalService)
structure SimpleLocalServiceReference {}

operation SelfReflection {
  input := {
    @required
    client: SimpleLocalServiceReference
  }
  output := {
    @required
    greeting: String
  }
}

operation HelloWorld {
  input := {
  }
  output := {
    @required
    greeting: String
  }
}