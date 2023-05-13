// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProvidersTestVectorKeys; namespace AWS.Cryptography.MaterialProvidersTestVectorKeys {
 public class KeyVectorsConfig {
 private string _keyManifiestPath ;
 public string KeyManifiestPath {
 get { return this._keyManifiestPath; }
 set { this._keyManifiestPath = value; }
}
 public bool IsSetKeyManifiestPath () {
 return this._keyManifiestPath != null;
}
 public void Validate() {
 if (!IsSetKeyManifiestPath()) throw new System.ArgumentException("Missing value for required property 'KeyManifiestPath'");

}
}
}
