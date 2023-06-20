// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateCryptographicMaterialsCacheInput {
 private int? _entryCapacity ;
 private int? _entryPruningTailSize ;
 private int? _gracePeriod ;
 private int? _graceInterval ;
 private int? _fanOut ;
 public int EntryCapacity {
 get { return this._entryCapacity.GetValueOrDefault(); }
 set { this._entryCapacity = value; }
}
 public bool IsSetEntryCapacity () {
 return this._entryCapacity.HasValue;
}
 public int EntryPruningTailSize {
 get { return this._entryPruningTailSize.GetValueOrDefault(); }
 set { this._entryPruningTailSize = value; }
}
 public bool IsSetEntryPruningTailSize () {
 return this._entryPruningTailSize.HasValue;
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
 public void Validate() {
 if (!IsSetEntryCapacity()) throw new System.ArgumentException("Missing value for required property 'EntryCapacity'");

}
}
}
