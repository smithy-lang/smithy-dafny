// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/$dafnyModuleName:LTypes.dfy"

module {:options "--function-syntax:4"}{:extern $dafnyNamespace:S} Com.Amazonaws.$sdkID:L refines Abstract$dafnyModuleName:LService {

  function Default$sdkID:LClientConfigType() : $sdkID:LClientConfigType {
    $sdkID:LClientConfigType
  }

}
