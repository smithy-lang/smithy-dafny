// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using Simple.Aggregate; namespace Simple.Aggregate {
 public class GetAggregateInput {
 private System.Collections.Generic.List<string> _simpleStringList ;
 private System.Collections.Generic.List<Simple.Aggregate.StructureListElement> _structureList ;
 private System.Collections.Generic.Dictionary<string, string> _simpleStringMap ;
 private System.Collections.Generic.Dictionary<string, int> _simpleIntegerMap ;
 private Simple.Aggregate.Deeply _very ;
 public System.Collections.Generic.List<string> SimpleStringList {
 get { return this._simpleStringList; }
 set { this._simpleStringList = value; }
}
 public bool IsSetSimpleStringList () {
 return this._simpleStringList != null;
}
 public System.Collections.Generic.List<Simple.Aggregate.StructureListElement> StructureList {
 get { return this._structureList; }
 set { this._structureList = value; }
}
 public bool IsSetStructureList () {
 return this._structureList != null;
}
 public System.Collections.Generic.Dictionary<string, string> SimpleStringMap {
 get { return this._simpleStringMap; }
 set { this._simpleStringMap = value; }
}
 public bool IsSetSimpleStringMap () {
 return this._simpleStringMap != null;
}
 public System.Collections.Generic.Dictionary<string, int> SimpleIntegerMap {
 get { return this._simpleIntegerMap; }
 set { this._simpleIntegerMap = value; }
}
 public bool IsSetSimpleIntegerMap () {
 return this._simpleIntegerMap != null;
}
 public Simple.Aggregate.Deeply Very {
 get { return this._very; }
 set { this._very = value; }
}
 public bool IsSetVery () {
 return this._very != null;
}
 public void Validate() {
 
}
}
}
