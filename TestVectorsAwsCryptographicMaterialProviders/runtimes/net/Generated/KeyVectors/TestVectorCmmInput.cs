// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProvidersTestVectorKeys;
namespace AWS.Cryptography.MaterialProvidersTestVectorKeys
{
  public class TestVectorCmmInput
  {
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription _keyDescription;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.CmmOperation _forOperation;
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription KeyDescription
    {
      get { return this._keyDescription; }
      set { this._keyDescription = value; }
    }
    public bool IsSetKeyDescription()
    {
      return this._keyDescription != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.CmmOperation ForOperation
    {
      get { return this._forOperation; }
      set { this._forOperation = value; }
    }
    public bool IsSetForOperation()
    {
      return this._forOperation != null;
    }
    public void Validate()
    {
      if (!IsSetKeyDescription()) throw new System.ArgumentException("Missing value for required property 'KeyDescription'");
      if (!IsSetForOperation()) throw new System.ArgumentException("Missing value for required property 'ForOperation'");

    }
  }
}
