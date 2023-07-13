// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateCryptographicMaterialsCacheInput {
 private AWS.Cryptography.MaterialProviders.CacheType _cache ;
 public AWS.Cryptography.MaterialProviders.CacheType Cache {
 get { return this._cache; }
 set { this._cache = value; }
}
 public bool IsSetCache () {
 return this._cache != null;
}
 public void Validate() {
 if (!IsSetCache()) throw new System.ArgumentException("Missing value for required property 'Cache'");

}
}
}
