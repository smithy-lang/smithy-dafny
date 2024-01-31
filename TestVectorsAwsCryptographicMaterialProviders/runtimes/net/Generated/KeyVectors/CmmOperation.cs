// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
using AWS.Cryptography.MaterialProvidersTestVectorKeys;
namespace AWS.Cryptography.MaterialProvidersTestVectorKeys
{
  using Amazon.Runtime;
  public class CmmOperation : ConstantClass
  {


    public static readonly CmmOperation ENCRYPT = new CmmOperation("ENCRYPT");

    public static readonly CmmOperation DECRYPT = new CmmOperation("DECRYPT");
    public static readonly CmmOperation[] Values =  {
 DECRYPT , ENCRYPT
};
    public CmmOperation(string value) : base(value) { }
  }
}
