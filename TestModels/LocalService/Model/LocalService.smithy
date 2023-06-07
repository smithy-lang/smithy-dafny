// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.localService

@aws.polymorph#localService(
  sdkId: "SimpleLocalService",
  config: SimpleLocalServiceConfig,
)
service SimpleLocalService {
  version: "2021-11-01",
  resources: [],
  operations: [],
  errors: [ SimpleLocalServiceException ],
}

structure SimpleLocalServiceConfig {}

@error("client")
structure SimpleLocalServiceException {
  @required
  message: String,
}
