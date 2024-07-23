// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package $dafnyNamespace:L;

import static software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.smithy.dafny.conversion.ToNative.Simple.String;

import StandardLibraryInterop_Compile.WrappersInterop;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;
import dafny.DafnySequence;
import software.amazon.awssdk.auth.credentials.ProfileCredentialsProvider;
import software.amazon.awssdk.regions.Region;
import software.amazon.awssdk.regions.providers.DefaultAwsRegionProviderChain;
import $sdkClientNamespace:L.$sdkClientName:L;
import $dafnyNamespace:L.types.Error;
import $dafnyNamespace:L.types.I$sdkID:LClient;

public class __default
  extends $dafnyNamespace:L._ExternBase___default {

  public static Result<I$sdkID:LClient, Error> $sdkID:LClient() {
    try {
      Region region = new DefaultAwsRegionProviderChain().getRegion();
      final $sdkClientName:L nativeClient = $sdkClientName:L
        .builder()
        .region(region)
        .build();

      I$sdkID:LClient shim = new Shim(nativeClient, region.toString());
      return CreateSuccessOfClient(shim);
    } catch (Exception e) {
      Error dafny_error = Error.create_Opaque(e);
      return CreateFailureOfError(dafny_error);
    }
  }
}
