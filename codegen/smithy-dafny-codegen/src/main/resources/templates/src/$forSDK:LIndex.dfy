// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/$dafnyModuleName:LTypes.dfy"

module {:options "--function-syntax:4"}{:extern $dafnyNamespace:S} Com.Amazonaws.$service:L refines Abstract$dafnyModuleName:LService {

  function Default$service:LClientConfigType() : $service:LClientConfigType {
    $service:LClientConfigType
  }

}
