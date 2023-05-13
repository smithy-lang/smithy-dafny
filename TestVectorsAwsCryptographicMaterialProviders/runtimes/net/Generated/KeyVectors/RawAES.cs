// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProvidersTestVectorKeys; namespace AWS.Cryptography.MaterialProvidersTestVectorKeys {
 public class RawAES {
 private string _keyId ;
 private string _providerId ;
 public string KeyId {
 get { return this._keyId; }
 set { this._keyId = value; }
}
 public bool IsSetKeyId () {
 return this._keyId != null;
}
 public string ProviderId {
 get { return this._providerId; }
 set { this._providerId = value; }
}
 public bool IsSetProviderId () {
 return this._providerId != null;
}
 public void Validate() {
 if (!IsSetKeyId()) throw new System.ArgumentException("Missing value for required property 'KeyId'");
 if (!IsSetProviderId()) throw new System.ArgumentException("Missing value for required property 'ProviderId'");

}
}
}
