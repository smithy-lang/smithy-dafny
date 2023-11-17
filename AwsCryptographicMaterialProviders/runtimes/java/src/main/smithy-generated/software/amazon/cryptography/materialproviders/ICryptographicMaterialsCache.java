// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders;

import software.amazon.cryptography.materialproviders.model.DeleteCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.GetCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.GetCacheEntryOutput;
import software.amazon.cryptography.materialproviders.model.PutCacheEntryInput;
import software.amazon.cryptography.materialproviders.model.UpdateUsageMetadataInput;

public interface ICryptographicMaterialsCache {
  void DeleteCacheEntry(DeleteCacheEntryInput input);

  GetCacheEntryOutput GetCacheEntry(GetCacheEntryInput input);

  void PutCacheEntry(PutCacheEntryInput input);

  void UpdateUsageMetadata(UpdateUsageMetadataInput input);
}
