// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProvidersTestVectorKeys;
namespace AWS.Cryptography.MaterialProvidersTestVectorKeys
{
  public class KeyVectorsConfig
  {
    private string _keyManifestPath;
    public string KeyManifestPath
    {
      get { return this._keyManifestPath; }
      set { this._keyManifestPath = value; }
    }
    public bool IsSetKeyManifestPath()
    {
      return this._keyManifestPath != null;
    }
    public void Validate()
    {
      if (!IsSetKeyManifestPath()) throw new System.ArgumentException("Missing value for required property 'KeyManifestPath'");

    }
  }
}
