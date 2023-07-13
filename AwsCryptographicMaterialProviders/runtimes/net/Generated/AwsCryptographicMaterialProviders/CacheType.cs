// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using AWS.Cryptography.MaterialProviders; namespace AWS.Cryptography.MaterialProviders {
 public class CacheType {
 private AWS.Cryptography.MaterialProviders.DefaultCache _defaultCache ;
 private AWS.Cryptography.MaterialProviders.NoCache _noCache ;
 private AWS.Cryptography.MaterialProviders.SingleThreadedCache _singleThreadedCache ;
 private AWS.Cryptography.MaterialProviders.MultiThreadedCache _multiThreadedCache ;
 private AWS.Cryptography.MaterialProviders.StormTrackingCache _stormTrackingCache ;
 public AWS.Cryptography.MaterialProviders.DefaultCache DefaultCache {
 get { return this._defaultCache; }
 set { this._defaultCache = value; }
}
 public bool IsSetDefaultCache () {
 return this._defaultCache != null;
}
 public AWS.Cryptography.MaterialProviders.NoCache NoCache {
 get { return this._noCache; }
 set { this._noCache = value; }
}
 public bool IsSetNoCache () {
 return this._noCache != null;
}
 public AWS.Cryptography.MaterialProviders.SingleThreadedCache SingleThreadedCache {
 get { return this._singleThreadedCache; }
 set { this._singleThreadedCache = value; }
}
 public bool IsSetSingleThreadedCache () {
 return this._singleThreadedCache != null;
}
 public AWS.Cryptography.MaterialProviders.MultiThreadedCache MultiThreadedCache {
 get { return this._multiThreadedCache; }
 set { this._multiThreadedCache = value; }
}
 public bool IsSetMultiThreadedCache () {
 return this._multiThreadedCache != null;
}
 public AWS.Cryptography.MaterialProviders.StormTrackingCache StormTrackingCache {
 get { return this._stormTrackingCache; }
 set { this._stormTrackingCache = value; }
}
 public bool IsSetStormTrackingCache () {
 return this._stormTrackingCache != null;
}
 public void Validate() {
 var numberOfPropertiesSet = Convert.ToUInt16(IsSetDefaultCache()) +
 Convert.ToUInt16(IsSetNoCache()) +
 Convert.ToUInt16(IsSetSingleThreadedCache()) +
 Convert.ToUInt16(IsSetMultiThreadedCache()) +
 Convert.ToUInt16(IsSetStormTrackingCache()) ;
 if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

 if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

}
}
}
