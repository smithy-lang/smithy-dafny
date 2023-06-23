package software.amazon.cryptography.internaldafny;

import LocalCMC_Compile.LocalCMC;

@SuppressWarnings({"unchecked", "deprecation"})
public class SynchronizedLocalCMC implements software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache {
  private LocalCMC wrapped;

  public SynchronizedLocalCMC(LocalCMC wrapped)
  {
    (this).wrapped = wrapped;
  }

  public synchronized Wrappers_Compile.Result<dafny.Tuple0, software.amazon.cryptography.materialproviders.internaldafny.types.Error> PutCacheEntry(software.amazon.cryptography.materialproviders.internaldafny.types.PutCacheEntryInput input)
  {
    return wrapped.PutCacheEntry(input);
  }
  public synchronized Wrappers_Compile.Result<dafny.Tuple0, software.amazon.cryptography.materialproviders.internaldafny.types.Error> UpdateUsageMetadata(software.amazon.cryptography.materialproviders.internaldafny.types.UpdateUsageMetadataInput input)
  {
    return wrapped.UpdateUsageMetadata(input);
  }
  public synchronized Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types.Error> GetCacheEntry(software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryInput input)
  {
    return wrapped.GetCacheEntry(input);
  }
  public synchronized Wrappers_Compile.Result<dafny.Tuple0, software.amazon.cryptography.materialproviders.internaldafny.types.Error> DeleteCacheEntry(software.amazon.cryptography.materialproviders.internaldafny.types.DeleteCacheEntryInput input)
  {
    return wrapped.DeleteCacheEntry(input);
  }

  public synchronized Wrappers_Compile.Result<dafny.Tuple0, software.amazon.cryptography.materialproviders.internaldafny.types.Error> PutCacheEntry_k(software.amazon.cryptography.materialproviders.internaldafny.types.PutCacheEntryInput input)
  {
    return wrapped.PutCacheEntry(input);
  }
  public synchronized Wrappers_Compile.Result<dafny.Tuple0, software.amazon.cryptography.materialproviders.internaldafny.types.Error> UpdateUsageMetadata_k(software.amazon.cryptography.materialproviders.internaldafny.types.UpdateUsageMetadataInput input)
  {
    return wrapped.UpdateUsageMetadata(input);
  }
  public synchronized Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types.Error> GetCacheEntry_k(software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryInput input)
  {
    return wrapped.GetCacheEntry(input);
  }
  public synchronized Wrappers_Compile.Result<dafny.Tuple0, software.amazon.cryptography.materialproviders.internaldafny.types.Error> DeleteCacheEntry_k(software.amazon.cryptography.materialproviders.internaldafny.types.DeleteCacheEntryInput input)
  {
    return wrapped.DeleteCacheEntry(input);
  }

  @Override
  public java.lang.String toString() {
    return "LocalCMC_Compile.SynchronizedLocalCMC";
  }
}
