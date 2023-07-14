// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class DefaultCache {
 private int? _entryCapacity ;
 public int EntryCapacity {
 get { return this._entryCapacity.GetValueOrDefault(); }
 set { this._entryCapacity = value; }
}
 public bool IsSetEntryCapacity () {
 return this._entryCapacity.HasValue;
}
 public void Validate() {
 if (!IsSetEntryCapacity()) throw new System.ArgumentException("Missing value for required property 'EntryCapacity'");

}
}
}
