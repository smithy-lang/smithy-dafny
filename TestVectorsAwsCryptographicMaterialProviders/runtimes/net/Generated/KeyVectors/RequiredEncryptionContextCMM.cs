// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProvidersTestVectorKeys;
namespace AWS.Cryptography.MaterialProvidersTestVectorKeys
{
  public class RequiredEncryptionContextCMM
  {
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription _underlying;
    private System.Collections.Generic.List<string> _requiredEncryptionContextKeys;
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.KeyDescription Underlying
    {
      get { return this._underlying; }
      set { this._underlying = value; }
    }
    public bool IsSetUnderlying()
    {
      return this._underlying != null;
    }
    public System.Collections.Generic.List<string> RequiredEncryptionContextKeys
    {
      get { return this._requiredEncryptionContextKeys; }
      set { this._requiredEncryptionContextKeys = value; }
    }
    public bool IsSetRequiredEncryptionContextKeys()
    {
      return this._requiredEncryptionContextKeys != null;
    }
    public void Validate()
    {
      if (!IsSetUnderlying()) throw new System.ArgumentException("Missing value for required property 'Underlying'");
      if (!IsSetRequiredEncryptionContextKeys()) throw new System.ArgumentException("Missing value for required property 'RequiredEncryptionContextKeys'");

    }
  }
}
