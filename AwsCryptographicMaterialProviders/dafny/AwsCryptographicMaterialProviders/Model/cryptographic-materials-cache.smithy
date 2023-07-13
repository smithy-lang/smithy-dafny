namespace aws.cryptography.materialProviders

use aws.polymorph#reference
use aws.polymorph#positional
use aws.polymorph#extendable
use aws.polymorph#javadoc

@range(min: 1)
integer NaturalNumber

@aws.polymorph#mutableLocalState
@aws.polymorph#extendable
resource CryptographicMaterialsCache {

  //= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#overview
  //= type=implication
  //# Cryptographic materials cache (CMC) is used by the [caching cryptographic materials manager (CMM)](caching-cmm.md)
  //# to store cryptographic materials for reuse.
  //# This document describes the interface that all CMCs MUST implement.
  operations: [PutCacheEntry, GetCacheEntry, UpdateUsageMetadata, DeleteCacheEntry]
}

@aws.polymorph#reference(resource: CryptographicMaterialsCache)
structure CryptographicMaterialsCacheReference {}

//= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#put-cache-entry
//= type=implication
//# This operation MUST NOT return the inserted cache entry.
operation PutCacheEntry {
  input: PutCacheEntryInput,
}

structure PutCacheEntryInput {
  @required
  identifier: Blob,
  @required
  materials: Materials,
  @required
  creationTime: PositiveLong,
  @required
  //= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#put-cache-entry
  //= type=implication
  //# The cache entry MUST include all [usage metadata](#usage-metadata)
  //# since this information can not be updated after the put operation.
  expiryTime: PositiveLong,
  messagesUsed: PositiveInteger,
  bytesUsed: PositiveInteger,
}

operation GetCacheEntry {
  input: GetCacheEntryInput,
  output: GetCacheEntryOutput,
}

structure GetCacheEntryInput {
  @required
  identifier: Blob,
  bytesUsed: Long

}

//= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#cache-entry
//= type=implication
//# A cache entry represents an entry in the cryptographic materials cache
//# and MUST have the following information.
//# 
//# - [Materials](#materials)
//# - [Creation Time](#creation-time)
//# - [Expiry Time](#expiry-time)
//# - [Usage Metadata](#usage-metadata)
structure GetCacheEntryOutput {
  @required
  materials: Materials,
  @required
  creationTime: PositiveLong,
  //= aws-encryption-sdk-specification/framework/cryptographic-materials-cache.md#time-to-live-ttl
  //= type=implication
  //# Each cache entry has a time-to-live (TTL)
  //# that represents a point in time at which the cache entry
  //# MUST be considered invalid.
  @required
  expiryTime: PositiveLong,
  @required
  messagesUsed: PositiveInteger,
  @required
  bytesUsed: PositiveInteger,
}

union Materials {
  Encryption: EncryptionMaterials,
  Decryption: DecryptionMaterials,
  BranchKey: aws.cryptography.keyStore#BranchKeyMaterials,
  BeaconKey: aws.cryptography.keyStore#BeaconKeyMaterials
}

operation DeleteCacheEntry {
  input: DeleteCacheEntryInput
}

structure DeleteCacheEntryInput {
  @required
  identifier: Blob
}

operation UpdateUsageMetadata {
  input: UpdateUsageMetadataInput
}

structure UpdateUsageMetadataInput {
  @required
  identifier: Blob,
  @required
  bytesUsed: PositiveInteger,
}

@error("client")
structure EntryDoesNotExist {
  @required
  message: String,
}

@error("client")
structure EntryAlreadyExists {
  @required
  message: String,
}

///////////////////
// Materials Cache Constructors

@positional
structure CreateCryptographicMaterialsCacheOutput {
  @required
  materialsCache: CryptographicMaterialsCacheReference 
}

operation CreateCryptographicMaterialsCache {
  input: CreateCryptographicMaterialsCacheInput,
  output: CreateCryptographicMaterialsCacheOutput,
}

@javadoc("The best choice for most situations. Probably a StormTrackingCache.")
structure DefaultCache {
  @required
  @javadoc("Maximum number of entries cached.")
  entryCapacity: NaturalNumber
}

@javadoc("Nothing should ever be cached.")
structure NoCache {}

@javadoc("A cache that is NOT safe for use in a multi threaded environment.")
structure SingleThreadedCache {
  //= aws-encryption-sdk-specification/framework/local-cryptographic-materials-cache.md#initialization
  //= type=implication
  //# On initialization of the local CMC,
  //# the caller MUST provide the following:
  //#
  //# - [Entry Capacity](#entry-capacity)
  //#
  //# The local CMC MUST also define the following:
  //#
  //# - [Entry Pruning Tail Size](#entry-pruning-tail-size)
  @required
  @javadoc("Maximum number of entries cached.")
  entryCapacity: NaturalNumber,

  @javadoc("Number of entries to prune at a time.")
  entryPruningTailSize: NaturalNumber,
}

@javadoc("A cache that is safe for use in a multi threaded environment, but no extra functionality.")
structure MultiThreadedCache {
  @required
  @javadoc("Maximum number of entries cached.")
  entryCapacity: NaturalNumber,

  @javadoc("Number of entries to prune at a time.")
  entryPruningTailSize: NaturalNumber,
}

@javadoc("A cache that is safe for use in a multi threaded environment,
and tries to prevent redundant or overly parallel backend calls.")
structure StormTrackingCache {
  @required
  @javadoc("Maximum number of entries cached.")
  entryCapacity: NaturalNumber,

  @javadoc("Number of entries to prune at a time.")
  entryPruningTailSize: NaturalNumber,

  @required
  @javadoc("How many seconds before expiration should an attempt be made to refresh the materials.
  If zero, use a simple cache with no storm tracking.")
  gracePeriod: NaturalNumber,

  @required
  @javadoc("How many seconds between attempts to refresh the materials.")
  graceInterval: NaturalNumber,

  @required
  @javadoc("How many simultaneous attempts to refresh the materials.")
  fanOut: NaturalNumber,

  @required
  @javadoc("How many seconds until an attempt to refresh the materials should be forgotten.")
  inFlightTTL: NaturalNumber,

  @required
  @javadoc("How many milliseconds should a thread sleep if fanOut is exceeded.")
  sleepMilli: NaturalNumber,
}

union CacheType {
  defaultCache : DefaultCache,
  noCache: NoCache,
  singleThreadedCache: SingleThreadedCache,
  multiThreadedCache: MultiThreadedCache,
  stormTrackingCache: StormTrackingCache
}

structure CreateCryptographicMaterialsCacheInput {
  @required
  @javadoc("Which type of local cache to use.")
  cache: CacheType
}
