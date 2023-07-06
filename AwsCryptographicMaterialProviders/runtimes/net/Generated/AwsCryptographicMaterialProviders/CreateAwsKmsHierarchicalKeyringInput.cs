// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateAwsKmsHierarchicalKeyringInput {
 private string _branchKeyId ;
 private AWS.Cryptography.MaterialProviders.IBranchKeyIdSupplier _branchKeyIdSupplier ;
 private AWS.Cryptography.KeyStore.KeyStore _keyStore ;
 private long? _ttlSeconds ;
 private int? _maxCacheSize ;
 private int? _gracePeriod ;
 private int? _graceInterval ;
 private int? _fanOut ;
 private int? _inFlightTTL ;
 public string BranchKeyId {
 get { return this._branchKeyId; }
 set { this._branchKeyId = value; }
}
 public bool IsSetBranchKeyId () {
 return this._branchKeyId != null;
}
 public AWS.Cryptography.MaterialProviders.IBranchKeyIdSupplier BranchKeyIdSupplier {
 get { return this._branchKeyIdSupplier; }
 set { this._branchKeyIdSupplier = value; }
}
 public bool IsSetBranchKeyIdSupplier () {
 return this._branchKeyIdSupplier != null;
}
 public AWS.Cryptography.KeyStore.KeyStore KeyStore {
 get { return this._keyStore; }
 set { this._keyStore = value; }
}
 public bool IsSetKeyStore () {
 return this._keyStore != null;
}
 public long TtlSeconds {
 get { return this._ttlSeconds.GetValueOrDefault(); }
 set { this._ttlSeconds = value; }
}
 public bool IsSetTtlSeconds () {
 return this._ttlSeconds.HasValue;
}
 public int MaxCacheSize {
 get { return this._maxCacheSize.GetValueOrDefault(); }
 set { this._maxCacheSize = value; }
}
 public bool IsSetMaxCacheSize () {
 return this._maxCacheSize.HasValue;
}
 public int GracePeriod {
 get { return this._gracePeriod.GetValueOrDefault(); }
 set { this._gracePeriod = value; }
}
 public bool IsSetGracePeriod () {
 return this._gracePeriod.HasValue;
}
 public int GraceInterval {
 get { return this._graceInterval.GetValueOrDefault(); }
 set { this._graceInterval = value; }
}
 public bool IsSetGraceInterval () {
 return this._graceInterval.HasValue;
}
 public int FanOut {
 get { return this._fanOut.GetValueOrDefault(); }
 set { this._fanOut = value; }
}
 public bool IsSetFanOut () {
 return this._fanOut.HasValue;
}
 public int InFlightTTL {
 get { return this._inFlightTTL.GetValueOrDefault(); }
 set { this._inFlightTTL = value; }
}
 public bool IsSetInFlightTTL () {
 return this._inFlightTTL.HasValue;
}
 public void Validate() {
 if (!IsSetKeyStore()) throw new System.ArgumentException("Missing value for required property 'KeyStore'");
 if (!IsSetTtlSeconds()) throw new System.ArgumentException("Missing value for required property 'TtlSeconds'");

}
}
}
