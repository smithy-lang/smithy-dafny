// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProvidersTestVectorKeys; namespace AWS.Cryptography.MaterialProvidersTestVectorKeys {
 public class KmsRsaKeyring {
 private string _keyId ;
 private Amazon.KeyManagementService.EncryptionAlgorithmSpec _encryptionAlgorithm ;
 public string KeyId {
 get { return this._keyId; }
 set { this._keyId = value; }
}
 public bool IsSetKeyId () {
 return this._keyId != null;
}
 public Amazon.KeyManagementService.EncryptionAlgorithmSpec EncryptionAlgorithm {
 get { return this._encryptionAlgorithm; }
 set { this._encryptionAlgorithm = value; }
}
 public bool IsSetEncryptionAlgorithm () {
 return this._encryptionAlgorithm != null;
}
 public void Validate() {
 if (!IsSetKeyId()) throw new System.ArgumentException("Missing value for required property 'KeyId'");
 if (!IsSetEncryptionAlgorithm()) throw new System.ArgumentException("Missing value for required property 'EncryptionAlgorithm'");

}
}
}
