// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using Simple.Aggregate; namespace Simple.Aggregate {
 public class StructureListElement {
 private string _s ;
 private int? _i ;
 public string S {
 get { return this._s; }
 set { this._s = value; }
}
 public bool IsSetS () {
 return this._s != null;
}
 public int I {
 get { return this._i.GetValueOrDefault(); }
 set { this._i = value; }
}
 public bool IsSetI () {
 return this._i.HasValue;
}
 public void Validate() {
 
}
}
}
