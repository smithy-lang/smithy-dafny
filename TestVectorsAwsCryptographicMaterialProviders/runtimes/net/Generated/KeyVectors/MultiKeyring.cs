// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProvidersTestVectorKeys;
namespace AWS.Cryptography.MaterialProvidersTestVectorKeys
{
  public class MultiKeyring
  {
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription _generator;
    private System.Collections.Generic.List<AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription> _childKeyrings;
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription Generator
    {
      get { return this._generator; }
      set { this._generator = value; }
    }
    public bool IsSetGenerator()
    {
      return this._generator != null;
    }
    public System.Collections.Generic.List<AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription> ChildKeyrings
    {
      get { return this._childKeyrings; }
      set { this._childKeyrings = value; }
    }
    public bool IsSetChildKeyrings()
    {
      return this._childKeyrings != null;
    }
    public void Validate()
    {
      if (!IsSetChildKeyrings()) throw new System.ArgumentException("Missing value for required property 'ChildKeyrings'");

    }
  }
}
