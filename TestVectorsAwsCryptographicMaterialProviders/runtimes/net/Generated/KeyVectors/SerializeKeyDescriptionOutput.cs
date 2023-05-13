// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProvidersTestVectorKeys; namespace AWS.Cryptography.MaterialProvidersTestVectorKeys {
 public class SerializeKeyDescriptionOutput {
 private System.IO.MemoryStream _json ;
 public System.IO.MemoryStream Json {
 get { return this._json; }
 set { this._json = value; }
}
 public bool IsSetJson () {
 return this._json != null;
}
 public void Validate() {
 if (!IsSetJson()) throw new System.ArgumentException("Missing value for required property 'Json'");

}
}
}
