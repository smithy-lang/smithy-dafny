// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProvidersTestVectorKeys; namespace AWS.Cryptography.MaterialProvidersTestVectorKeys {
 public class TestVectorKeyringInput {
 private AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription _keyDescription ;
 public AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription KeyDescription {
 get { return this._keyDescription; }
 set { this._keyDescription = value; }
}
 public bool IsSetKeyDescription () {
 return this._keyDescription != null;
}
 public void Validate() {
 if (!IsSetKeyDescription()) throw new System.ArgumentException("Missing value for required property 'KeyDescription'");

}
}
}
