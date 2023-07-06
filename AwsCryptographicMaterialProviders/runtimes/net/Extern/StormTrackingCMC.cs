// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using software.amazon.cryptography.primitives.internaldafny.types;

namespace software.amazon.cryptography.internaldafny.StormTrackingCMC
{
  public partial class StormTrackingCMC : software.amazon.cryptography.materialproviders.internaldafny.types.ICryptographicMaterialsCache
  {
    public StormTracker_Compile.StormTracker wrapped;

    public StormTrackingCMC(StormTracker_Compile.StormTracker cmc)
    {
      this.wrapped = cmc;
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.Synchronized)]
    public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> PutCacheEntry(software.amazon.cryptography.materialproviders.internaldafny.types._IPutCacheEntryInput input)
    {
      return PutCacheEntry_k(input);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.Synchronized)]
    public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> UpdateUsageMetadata(software.amazon.cryptography.materialproviders.internaldafny.types._IUpdateUsageMetadataInput input)
    {
      return UpdateUsageMetadata_k(input);
    }

    // NOT synchronized, as some sleeping might be involved
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetCacheEntry(software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryInput input)
    {
      return GetCacheEntry_k(input);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.Synchronized)]
    public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> DeleteCacheEntry(software.amazon.cryptography.materialproviders.internaldafny.types._IDeleteCacheEntryInput input)
    {
      return DeleteCacheEntry_k(input);
    }

    // This is the synchronization for GetCacheEntry and GetCacheEntry_k
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.Synchronized)]
    public Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>
      GetFromCacheInner(software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryInput input) {
      return wrapped.GetFromCache(input);
    }

    // NOT synchronized, as some sleeping might be involved
    public Wrappers_Compile._IResult<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError> GetCacheEntry_k(software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryInput input)
    {
      while (true) {
        Wrappers_Compile._IResult<StormTracker_Compile._ICacheState, software.amazon.cryptography.materialproviders.internaldafny.types._IError>
          result = GetFromCacheInner(input);
        if (result.is_Failure) {
          return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>
            .create_Failure((result).dtor_error);
        } else if (result.dtor_value.is_Full) {
          return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>
            .create_Success(result.dtor_value.dtor_data);
        } else if (result.dtor_value.is_EmptyFetch) {
          return Wrappers_Compile.Result<software.amazon.cryptography.materialproviders.internaldafny.types._IGetCacheEntryOutput, software.amazon.cryptography.materialproviders.internaldafny.types._IError>
              .create_Failure(software.amazon.cryptography.materialproviders.internaldafny.types.Error
                  .create_EntryDoesNotExist(Dafny.Sequence<char>.FromString("Entry does not exist")));
        } else {
          Thread.Sleep(50);
        }
      }
    }
    
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.Synchronized)]
    public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> PutCacheEntry_k(software.amazon.cryptography.materialproviders.internaldafny.types._IPutCacheEntryInput input)
    {
      return this.wrapped.PutCacheEntry(input);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.Synchronized)]
    public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> DeleteCacheEntry_k(software.amazon.cryptography.materialproviders.internaldafny.types._IDeleteCacheEntryInput input)
    {
      return this.wrapped.DeleteCacheEntry(input);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.Synchronized)]
    public Wrappers_Compile._IResult<_System._ITuple0, software.amazon.cryptography.materialproviders.internaldafny.types._IError> UpdateUsageMetadata_k(software.amazon.cryptography.materialproviders.internaldafny.types._IUpdateUsageMetadataInput input)
    {
      return this.wrapped.UpdateUsageMetadata(input);
    }
  }
}
