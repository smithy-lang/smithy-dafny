# AWS SDK for .NET v4 Migration Summary

## Overview
This document summarizes the changes made to migrate smithy-dafny from AWS SDK for .NET v3 to v4.

## Changes Made

### 1. Package Version Updates

**Template Files Updated:**
- `codegen/smithy-dafny-codegen/src/main/resources/templates/runtimes/net/$forSDK;L$sdkID;L.csproj`
  - Changed `AWSSDK.Core` from `3.7.100` → `4.0.0`
  - Changed `AWSSDK.$serviceName:L` from `3.7.100` → `4.0.0`

**Framework Versions (Unchanged):**
- Target Framework: `net6.0` (AWS SDK v4 supports .NET 6.0+)
- C# Language Version: `10` (compatible with generated Dafny code)

## Key AWS SDK v4 Breaking Changes to Be Aware Of

Based on the [official migration guide](https://docs.aws.amazon.com/sdk-for-net/v4/developer-guide/net-dg-v4.html), the following breaking changes may affect generated code:

### 1. Collection Properties Default to Null
**Impact:** HIGH - Requires code generation changes

In v3, collection properties were initialized to empty collections. In v4, they default to `null`.

**Example:**
```csharp
// V3 behavior (always non-null)
var response = await client.ListQueuesAsync(new ListQueuesRequest());
foreach (string qUrl in response.QueueUrls) { } // Safe

// V4 behavior (can be null)
var response = await client.ListQueuesAsync(new ListQueuesRequest());
if (response.QueueUrls != null) { // NULL CHECK REQUIRED
    foreach (string qUrl in response.QueueUrls) { }
}
```

**Action Required:** Update `TypeConversionCodegen.java` to add null checks when converting collections from AWS SDK types to Dafny types.

### 2. Value Type Properties Are Now Nullable
**Impact:** MEDIUM

Properties using value types (int, long, double, bool, DateTime, etc.) are now nullable value types.

**Example:**
```csharp
// V3
public int Count { get; set; }

// V4
public int? Count { get; set; }
```

**Action Required:** Verify that `DotNetNameResolver.baseTypeForOptionalMember()` correctly handles these nullable value types.

### 3. DateTime Properties Now Return UTC
**Impact:** LOW - Likely already handled correctly

DateTime properties that were returning local time now return UTC time.

**Action Required:** Review timestamp conversion logic in `TypeConversionCodegen.java`.

### 4. S3-Specific Changes
**Impact:** MEDIUM (if generating S3 clients)

- S3 clients in `us-east-1` can no longer access buckets in other regions
- S3 Encryption Client moved to separate package `Amazon.Extensions.S3.Encryption`
- `TaggingDirective` no longer automatically set to COPY
- Leading slashes no longer trimmed in CopyObject/CopyPart

### 5. DynamoDB-Specific Changes
**Impact:** MEDIUM (if generating DynamoDB clients)

- DynamoDBStreams moved to separate package `AWSSDK.DynamoDBStreams`
- Document Model now uses `System.Text.Json` instead of LitJson
- `RetrieveDateTimeInUtc` property default changed to `true`

## Code Generation Changes Required

### Priority 1: Collection Null Checks (CRITICAL)

**File:** `codegen/smithy-dafny-codegen/src/main/java/software/amazon/polymorph/smithydotnet/TypeConversionCodegen.java`

**Location:** Methods that convert AWS SDK responses to Dafny types, particularly:
- `generateFromDafnyConverter()` for List shapes
- `generateFromDafnyConverter()` for Map shapes

**Change Needed:**
```java
// Add null checks before iterating collections
// Example for List conversion:
if (value.Items != null) {
    return Dafny.Sequence.FromArray(
        value.Items.Select(item => /* convert item */).ToArray()
    );
} else {
    return Dafny.Sequence.Empty;
}
```

### Priority 2: Nullable Value Types

**File:** `codegen/smithy-dafny-codegen/src/main/java/software/amazon/polymorph/smithydotnet/DotNetNameResolver.java`

**Verification Needed:** Ensure `baseTypeForOptionalMember()` correctly identifies AWS SDK v4 value type properties as nullable.

### Priority 3: Test Model Updates

**Files:** All test model `.csproj` files in `TestModels/aws-sdks/*/runtimes/net/*.csproj`

**Action:** Update package versions to 4.0.0:
- `TestModels/aws-sdks/ddb/runtimes/net/DDBv2.csproj`
- `TestModels/aws-sdks/kms/runtimes/net/KMS.csproj`
- `TestModels/aws-sdks/s3/runtimes/net/S3.csproj`
- etc.

## Testing Strategy

1. **Unit Tests:** Verify type conversion logic handles null collections
2. **Integration Tests:** Test against actual AWS services with v4 SDK
3. **Regression Tests:** Ensure existing test models still work

## Rollback Plan

If issues arise, revert by changing package versions back to `3.7.100` in the template files.

## References

- [AWS SDK .NET v4 Migration Guide](https://docs.aws.amazon.com/sdk-for-net/v4/developer-guide/net-dg-v4.html)
- [AWS SDK .NET v4 GA Announcement](https://aws.amazon.com/blogs/developer/general-availability-of-aws-sdk-for-net-v4-0/)
- [End of Support for v3 Announcement](https://aws.amazon.com/blogs/devops/announcing-the-end-of-support-for-the-aws-sdk-for-net-v3/)
