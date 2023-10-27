# Changelog

## 1.0.2 (2023-10-18)

### Bug Fixes

    * CmpError must return custom error message (#118) (86abacc)
    * Deafult entryPruningTailSize (#93) (0344e9f)
    * Fix brittle concurrent test (#105) (#60) (c043162)
    * fix typo in encryption materials validation (cd6b0aa), closes #84
    * fix typo in encryption materials validation (89a234c)
    * Forward the underlying error (#90) (bc21551)

## 1.0.1 2023-07-26

### Fix

- Fixes a runtime check in `VersionKey` Key Store API that no longer checks for the CipherText length
  on the output of a KMS ReEncrypt API call.

## 1.0.0 2023-07-21

### Features

- Introduces Thread Safe Cryptographic Materials Caches (CMCs):
  - Storm Tracking Cache  
    Safe for use in a multi threaded environment,  
    tries to prevent redundant or overly parallel backend calls.  
    See [Spec changes](https://github.com/awslabs/aws-encryption-sdk-specification/blob/ce9a4062124edc5085c66a4f10742e15aa039b34/changes/2023-06-19_thread_safe_cache/change.md) for details.
  - Multi Threaded Cache  
    Safe for use in a multi threaded environment,  
    but no extra functionality

### BREAKING CHANGES

- CMCs:
  - Original Cryptographic Materials Cache has been renamed to Single Threaded Cache
  - `CreateCryptographicMaterialsCacheInput` now ONLY accepts `CacheType`,  
    which determines which, if any, of the three implemented CMCs will be returned.
  - The `DefaultCache` is `StormTrackingCache`
- `CreateAwsKmsHierarchicalKeyringInput`:
  - no longer has a `maxCacheSize` field
  - now has an optional `cache` field for a `CacheType`
- Hierarchical Keyring's Key Store:
  - The Hierarchical Keyring's Key Store's Data Structure has changed.  
    As such, entries persisted in the Key Store with prior versions of this library are NOT compatibale.  
    Instead, we recommend Creating a new DynamoDB Table for this version of the Key Store.
  - The Key Store's `CreateKeyInput` now takes:
    - An Optional `String branchKeyIdentifier`
    - An Optional `EncryptionContext encryptionContext`
      - This `encryptionContext` will be added to the Encryption Context sent to KMS prefixed with `aws-crypto-ec:`
  - Creating a Key now also calls KMS:ReEncrypt
  - `CreateKeyStore` no longer creates a GSI
  - The Encryption Context used with KMS' `GenerateDataKeyWithoutPlaintext` no longer include's the discarded GSI's `status`.
  - More details about the Key Store's changes are avaible in our Specification:
    - [2023-07-12 Update Key Store](https://github.com/awslabs/aws-encryption-sdk-specification/tree/master/changes/2023_7_12_update-keystore-structure)
    - [KeyStore Specification](https://github.com/awslabs/aws-encryption-sdk-specification/blob/master/framework/branch-key-store.md)

### Maintenance

- A variety of fixes to the libraries CI and testing

### Fix

- Fixes Required Encryption Context CMM and UpdateUsageMetadata names in smithy model

## 1.0.0-preview-3 2023-06-22

### Fix

- Fixes PutCacheEntry
  - PutCacheEntry will now update an entry.
    This simplifies using the cache in concurrent situations.
    Rather than having the caller implement some retry logic
    the cache will now update the entry.
- Fixes pom.xml to include runtime version of BouncyCastle and removes bundling of BC in the jar.

## 1.0.0-preview-2 2023-06-19

### Fix

- Fixes build file to correctly generate pom file with correct dependencies during release.

## 1.0.0-preview-1 2023-06-07

### Features

- Initial release of the AWS Cryptographic Material Providers Library.
  This release is considered a [developer preview](https://docs.aws.amazon.com/sdkref/latest/guide/maint-policy.html#version-life-cycle)
  and is not intended for production use cases.
