// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/ComAmazonawsGlueTypes.dfy"

module {:options "--function-syntax:4"}{:extern "software.amazon.cryptography.services.glue.internaldafny"} Com.Amazonaws.Glue refines AbstractComAmazonawsGlueService {

  function DefaultGlueClientConfigType() : GlueClientConfigType {
    GlueClientConfigType
  }

}
