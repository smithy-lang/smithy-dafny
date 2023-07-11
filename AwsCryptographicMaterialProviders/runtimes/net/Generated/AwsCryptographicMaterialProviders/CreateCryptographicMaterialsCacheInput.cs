// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CreateCryptographicMaterialsCacheInput {
 private int? _entryCapacity ;
 private int? _entryPruningTailSize ;
 private AWS.Cryptography.MaterialProviders.StormTrackerSettings _trackerSettings ;
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
 public AWS.Cryptography.MaterialProviders.StormTrackerSettings TrackerSettings {
 get { return this._trackerSettings; }
 set { this._trackerSettings = value; }
}
 public bool IsSetTrackerSettings () {
 return this._trackerSettings != null;
}
 public void Validate() {
 if (!IsSetEntryCapacity()) throw new System.ArgumentException("Missing value for required property 'EntryCapacity'");

}
}
}
