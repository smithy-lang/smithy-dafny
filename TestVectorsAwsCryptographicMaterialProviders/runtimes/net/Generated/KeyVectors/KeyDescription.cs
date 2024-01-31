// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProvidersTestVectorKeys;
namespace AWS.Cryptography.MaterialProvidersTestVectorKeys
{
  public class KeyDescription
  {
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.KMSInfo _kms;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.KmsMrkAware _kmsMrk;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.KmsMrkAwareDiscovery _kmsMrkDiscovery;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.RawRSA _rSA;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.RawAES _aES;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.StaticKeyring _static;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.KmsRsaKeyring _kmsRsa;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.HierarchyKeyring _hierarchy;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.MultiKeyring _multi;
    private AWS.Cryptography.MaterialProvidersTestVectorKeys.RequiredEncryptionContextCMM _requiredEncryptionContext;
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.KMSInfo Kms
    {
      get { return this._kms; }
      set { this._kms = value; }
    }
    public bool IsSetKms()
    {
      return this._kms != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.KmsMrkAware KmsMrk
    {
      get { return this._kmsMrk; }
      set { this._kmsMrk = value; }
    }
    public bool IsSetKmsMrk()
    {
      return this._kmsMrk != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.KmsMrkAwareDiscovery KmsMrkDiscovery
    {
      get { return this._kmsMrkDiscovery; }
      set { this._kmsMrkDiscovery = value; }
    }
    public bool IsSetKmsMrkDiscovery()
    {
      return this._kmsMrkDiscovery != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.RawRSA RSA
    {
      get { return this._rSA; }
      set { this._rSA = value; }
    }
    public bool IsSetRSA()
    {
      return this._rSA != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.RawAES AES
    {
      get { return this._aES; }
      set { this._aES = value; }
    }
    public bool IsSetAES()
    {
      return this._aES != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.StaticKeyring Static
    {
      get { return this._static; }
      set { this._static = value; }
    }
    public bool IsSetStatic()
    {
      return this._static != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.KmsRsaKeyring KmsRsa
    {
      get { return this._kmsRsa; }
      set { this._kmsRsa = value; }
    }
    public bool IsSetKmsRsa()
    {
      return this._kmsRsa != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.HierarchyKeyring Hierarchy
    {
      get { return this._hierarchy; }
      set { this._hierarchy = value; }
    }
    public bool IsSetHierarchy()
    {
      return this._hierarchy != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.MultiKeyring Multi
    {
      get { return this._multi; }
      set { this._multi = value; }
    }
    public bool IsSetMulti()
    {
      return this._multi != null;
    }
    public AWS.Cryptography.MaterialProvidersTestVectorKeys.RequiredEncryptionContextCMM RequiredEncryptionContext
    {
      get { return this._requiredEncryptionContext; }
      set { this._requiredEncryptionContext = value; }
    }
    public bool IsSetRequiredEncryptionContext()
    {
      return this._requiredEncryptionContext != null;
    }
    public void Validate()
    {
      var numberOfPropertiesSet = Convert.ToUInt16(IsSetKms()) +
      Convert.ToUInt16(IsSetKmsMrk()) +
      Convert.ToUInt16(IsSetKmsMrkDiscovery()) +
      Convert.ToUInt16(IsSetRSA()) +
      Convert.ToUInt16(IsSetAES()) +
      Convert.ToUInt16(IsSetStatic()) +
      Convert.ToUInt16(IsSetKmsRsa()) +
      Convert.ToUInt16(IsSetHierarchy()) +
      Convert.ToUInt16(IsSetMulti()) +
      Convert.ToUInt16(IsSetRequiredEncryptionContext());
      if (numberOfPropertiesSet == 0) throw new System.ArgumentException("No union value set");

      if (numberOfPropertiesSet > 1) throw new System.ArgumentException("Multiple union values set");

    }
  }
}
