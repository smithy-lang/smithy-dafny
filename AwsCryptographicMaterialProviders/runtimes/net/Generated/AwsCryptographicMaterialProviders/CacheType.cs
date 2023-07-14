// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CacheType {
 private AWS.Cryptography.MaterialProviders.DefaultCache _default ;
 private AWS.Cryptography.MaterialProviders.NoCache _no ;
 private AWS.Cryptography.MaterialProviders.SingleThreadedCache _singleThreaded ;
 private AWS.Cryptography.MaterialProviders.MultiThreadedCache _multiThreaded ;
 private AWS.Cryptography.MaterialProviders.StormTrackingCache _stormTracking ;
 public AWS.Cryptography.MaterialProviders.DefaultCache Default {
 get { return this._default; }
 set { this._default = value; }
}
 public bool IsSetDefault () {
 return this._default != null;
}
 public AWS.Cryptography.MaterialProviders.NoCache No {
 get { return this._no; }
 set { this._no = value; }
}
 public bool IsSetNo () {
 return this._no != null;
}
 public AWS.Cryptography.MaterialProviders.SingleThreadedCache SingleThreaded {
 get { return this._singleThreaded; }
 set { this._singleThreaded = value; }
}
 public bool IsSetSingleThreaded () {
 return this._singleThreaded != null;
}
 public AWS.Cryptography.MaterialProviders.MultiThreadedCache MultiThreaded {
 get { return this._multiThreaded; }
 set { this._multiThreaded = value; }
}
 public bool IsSetMultiThreaded () {
 return this._multiThreaded != null;
}
 public AWS.Cryptography.MaterialProviders.StormTrackingCache StormTracking {
 get { return this._stormTracking; }
 set { this._stormTracking = value; }
}
 public bool IsSetStormTracking () {
 return this._stormTracking != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetDefault()) +
 Convert.ToUInt16(IsSetNo()) +
 Convert.ToUInt16(IsSetSingleThreaded()) +
 Convert.ToUInt16(IsSetMultiThreaded()) +
 Convert.ToUInt16(IsSetStormTracking()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
