// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module SimpleLocalServiceTest {
  import SimpleLocalService
  import Types = SimpleLocalServiceTypes
  import opened Wrappers

  method TestClient(config: Types.SimpleLocalServiceConfig)
  {
    var client :- expect SimpleLocalService.SimpleLocalService(config);
  }

  method {:test} Test()
  {
    TestClient(SimpleLocalService.DefaultSimpleLocalServiceConfig());
  }

}
