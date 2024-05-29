// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/$dafnyTypesModuleName:L.dfy"

module {:options "--function-syntax:4"}{:extern $dafnyNamespace:S} Com.Amazonaws.$service:L refines AbstractComAmazonawsLakeformationService {

  function Default$service:LClientConfigType() : $service:LClientConfigType {
    $service:LClientConfigType
  }

}
