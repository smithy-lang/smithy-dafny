// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProvidersTestVectorKeys; namespace AWS.Cryptography.MaterialProvidersTestVectorKeys {
 public class RawRSA {
 private string _keyId ;
 private string _providerId ;
 private AWS.Cryptography.MaterialProviders.PaddingScheme _padding ;
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
 public AWS.Cryptography.MaterialProviders.PaddingScheme Padding {
 get { return this._padding; }
 set { this._padding = value; }
}
 public bool IsSetPadding () {
 return this._padding != null;
}
 public void Validate() {
 if (!IsSetKeyId()) throw new System.ArgumentException("Missing value for required property 'KeyId'");
 if (!IsSetProviderId()) throw new System.ArgumentException("Missing value for required property 'ProviderId'");
 if (!IsSetPadding()) throw new System.ArgumentException("Missing value for required property 'Padding'");

}
}
}
