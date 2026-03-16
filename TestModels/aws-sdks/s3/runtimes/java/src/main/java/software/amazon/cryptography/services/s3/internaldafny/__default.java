// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.cryptography.services.s3.internaldafny;

import static software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.smithy.dafny.conversion.ToNative.Simple.String;

import StandardLibraryInterop_Compile.WrappersInterop;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;
import dafny.DafnySequence;
import software.amazon.awssdk.auth.credentials.ProfileCredentialsProvider;
import software.amazon.awssdk.regions.Region;
import software.amazon.awssdk.regions.providers.DefaultAwsRegionProviderChain;
import software.amazon.awssdk.services.s3.S3Client;
import software.amazon.cryptography.services.s3.internaldafny.types.Error;
import software.amazon.cryptography.services.s3.internaldafny.types.IS3Client;

public class __default
  extends software.amazon.cryptography.services.s3.internaldafny._ExternBase___default {

  public static Result<IS3Client, Error> S3Client() {
    try {
      Region region = new DefaultAwsRegionProviderChain().getRegion();
      final S3Client nativeClient = S3Client
        .builder()
        .region(region)
        .build();

      IS3Client shim = new Shim(nativeClient, region.toString());
      return CreateSuccessOfClient(shim);
    } catch (Exception e) {
      Error dafny_error = Error.create_Opaque(e);
      return CreateFailureOfError(dafny_error);
    }
  }
}
