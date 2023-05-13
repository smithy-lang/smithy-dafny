// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProvidersTestVectorKeys; namespace AWS.Cryptography.MaterialProvidersTestVectorKeys {
 public class KmsMrkAwareDiscovery {
 private string _keyId ;
 private string _defaultMrkRegion ;
 private AWS.Cryptography.MaterialProviders.DiscoveryFilter _awsKmsDiscoveryFilter ;
 public string KeyId {
 get { return this._keyId; }
 set { this._keyId = value; }
}
 public bool IsSetKeyId () {
 return this._keyId != null;
}
 public string DefaultMrkRegion {
 get { return this._defaultMrkRegion; }
 set { this._defaultMrkRegion = value; }
}
 public bool IsSetDefaultMrkRegion () {
 return this._defaultMrkRegion != null;
}
 public AWS.Cryptography.MaterialProviders.DiscoveryFilter AwsKmsDiscoveryFilter {
 get { return this._awsKmsDiscoveryFilter; }
 set { this._awsKmsDiscoveryFilter = value; }
}
 public bool IsSetAwsKmsDiscoveryFilter () {
 return this._awsKmsDiscoveryFilter != null;
}
 public void Validate() {
 if (!IsSetKeyId()) throw new System.ArgumentException("Missing value for required property 'KeyId'");
 if (!IsSetDefaultMrkRegion()) throw new System.ArgumentException("Missing value for required property 'DefaultMrkRegion'");

}
}
}
