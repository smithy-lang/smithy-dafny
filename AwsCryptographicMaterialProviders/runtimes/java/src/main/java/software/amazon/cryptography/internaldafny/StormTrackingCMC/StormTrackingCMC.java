package software.amazon.cryptography.internaldafny.StormTrackingCMC;

import static software.amazon.cryptography.internaldafny.StormTrackingCMC._ExternBase___default.CreateGetCacheEntryFailure;
import static software.amazon.cryptography.internaldafny.StormTrackingCMC._ExternBase___default.CreateGetCacheEntrySuccess;

import StormTracker_Compile.CacheState;
import StormTracker_Compile.StormTracker;
import software.amazon.cryptography.materialproviders.internaldafny.*;
import software.amazon.cryptography.materialproviders.internaldafny.types.*;

@SuppressWarnings({ "unchecked", "deprecation" })
public class StormTrackingCMC
  implements
    software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache {

  private StormTracker wrapped;

  public StormTrackingCMC(StormTracker wrapped) {
    (this).wrapped = wrapped;
  }

  public synchronized Wrappers_Compile.Result<
    dafny.Tuple0,
    software.amazon.cryptography.materialproviders.internaldafny.types.Error
  > PutCacheEntry(
    software.amazon.cryptography.materialproviders.internaldafny.types.PutCacheEntryInput input
  ) {
    return wrapped.PutCacheEntry(input);
  }

  public synchronized Wrappers_Compile.Result<
    dafny.Tuple0,
    software.amazon.cryptography.materialproviders.internaldafny.types.Error
  > UpdateUsageMetadata(
    software.amazon.cryptography.materialproviders.internaldafny.types.UpdateUsageMetadataInput input
  ) {
    return wrapped.UpdateUsageMetadata(input);
  }

  // NOT synchronized, as some sleeping might be involved
  public Wrappers_Compile.Result<
    software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryOutput,
    software.amazon.cryptography.materialproviders.internaldafny.types.Error
  > GetCacheEntry(
    software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryInput input
  ) {
    return GetCacheEntry_k(input);
  }

  public synchronized Wrappers_Compile.Result<
    dafny.Tuple0,
    software.amazon.cryptography.materialproviders.internaldafny.types.Error
  > DeleteCacheEntry(
    software.amazon.cryptography.materialproviders.internaldafny.types.DeleteCacheEntryInput input
  ) {
    return wrapped.DeleteCacheEntry(input);
  }

  public synchronized Wrappers_Compile.Result<
    dafny.Tuple0,
    software.amazon.cryptography.materialproviders.internaldafny.types.Error
  > PutCacheEntry_k(
    software.amazon.cryptography.materialproviders.internaldafny.types.PutCacheEntryInput input
  ) {
    return wrapped.PutCacheEntry(input);
  }

  public synchronized Wrappers_Compile.Result<
    dafny.Tuple0,
    software.amazon.cryptography.materialproviders.internaldafny.types.Error
  > UpdateUsageMetadata_k(
    software.amazon.cryptography.materialproviders.internaldafny.types.UpdateUsageMetadataInput input
  ) {
    return wrapped.UpdateUsageMetadata(input);
  }

  // This is the synchronization for GetCacheEntry and GetCacheEntry_k
  public synchronized Wrappers_Compile.Result<
    CacheState,
    software.amazon.cryptography.materialproviders.internaldafny.types.Error
  > GetFromCacheInner(
    software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryInput input
  ) {
    return wrapped.GetFromCache(input);
  }

  // NOT synchronized, because we sleep. Calls GetFromCache which IS synchronized.
  public Wrappers_Compile.Result<
    software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryOutput,
    software.amazon.cryptography.materialproviders.internaldafny.types.Error
  > GetCacheEntry_k(
    software.amazon.cryptography.materialproviders.internaldafny.types.GetCacheEntryInput input
  ) {
    while (true) {
      Wrappers_Compile.Result<
        CacheState,
        software.amazon.cryptography.materialproviders.internaldafny.types.Error
      > result = GetFromCacheInner(input);
      if (result.is_Failure()) {
        return CreateGetCacheEntryFailure((result).dtor_error());
      } else if (result.dtor_value().is_Full()) {
        return CreateGetCacheEntrySuccess(result.dtor_value().dtor_data());
      } else if (result.dtor_value().is_EmptyFetch()) {
        return CreateGetCacheEntryFailure(
          software.amazon.cryptography.materialproviders.internaldafny.types.Error.create_EntryDoesNotExist(
            dafny.DafnySequence.asString("Entry does not exist")
          )
        );
      } else {
        try {
          Thread.sleep(wrapped.sleepMilli);
        } catch (Exception e) {}
      }
    }
  }

  public synchronized Wrappers_Compile.Result<
    dafny.Tuple0,
    software.amazon.cryptography.materialproviders.internaldafny.types.Error
  > DeleteCacheEntry_k(
    software.amazon.cryptography.materialproviders.internaldafny.types.DeleteCacheEntryInput input
  ) {
    return wrapped.DeleteCacheEntry(input);
  }

  @Override
  public java.lang.String toString() {
    return "StormTracker_Compile.StormTrackerCMC";
  }
}
