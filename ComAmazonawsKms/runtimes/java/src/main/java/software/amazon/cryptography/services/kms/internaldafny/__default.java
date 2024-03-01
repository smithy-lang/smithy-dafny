// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Extern code for AWS SDK for Java V2
package software.amazon.cryptography.services.kms.internaldafny;

import static software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence;
import static software.amazon.smithy.dafny.conversion.ToNative.Simple.String;

import StandardLibraryInterop_Compile.WrappersInterop;
import Wrappers_Compile.Option;
import Wrappers_Compile.Result;
import dafny.DafnySequence;
import software.amazon.awssdk.core.client.config.ClientOverrideConfiguration;
import software.amazon.awssdk.core.client.config.SdkAdvancedClientOption;
import software.amazon.awssdk.regions.Region;
import software.amazon.awssdk.regions.providers.AwsRegionProviderChain;
import software.amazon.awssdk.regions.providers.DefaultAwsRegionProviderChain;
import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.awssdk.services.kms.KmsClientBuilder;
import software.amazon.cryptography.services.kms.internaldafny.types.Error;
import software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient;

public class __default
  extends software.amazon.cryptography.services.kms.internaldafny._ExternBase___default {

  public static Result<IKMSClient, Error> KMSClient() {
    try {
      final KmsClientBuilder builder = KmsClient.builder();
      final AwsRegionProviderChain regionProvider =
        DefaultAwsRegionProviderChain.builder().build();
      final String region = regionProvider.getRegion().toString();
      final KmsClient client = builder
        .overrideConfiguration(
          ClientOverrideConfiguration
            .builder()
            .putAdvancedOption(
              SdkAdvancedClientOption.USER_AGENT_SUFFIX,
              UserAgentSuffix()
            )
            .build()
        )
        .build();
      final IKMSClient shim = new Shim(client, region);
      return CreateSuccessOfClient(shim);
    } catch (Exception e) {
      Error dafny_error = Error.create_KMSInternalException(
        WrappersInterop.CreateStringSome(CharacterSequence(e.getMessage()))
      );
      return CreateFailureOfError(dafny_error);
    }
  }

  public static Result<IKMSClient, Error> KMSClientForRegion(
    final DafnySequence<? extends Character> region
  ) {
    try {
      final char[] inputRegion = (char[]) region.toArray().unwrap();
      // The ESDK uses empty string as a kind of none.
      // In the case of an AWS KMS raw key identifier there is no region element
      // an so "" is used in this case.
      if (inputRegion.length == 0) {
        return KMSClient();
      }

      final String regionString = new String(inputRegion);
      final KmsClientBuilder builder = KmsClient.builder();
      final KmsClient client = builder
        .region(Region.of(regionString))
        .overrideConfiguration(
          ClientOverrideConfiguration
            .builder()
            .putAdvancedOption(
              SdkAdvancedClientOption.USER_AGENT_SUFFIX,
              UserAgentSuffix()
            )
            .build()
        )
        .build();
      final IKMSClient shim = new Shim(client, regionString);
      return CreateSuccessOfClient(shim);
    } catch (Exception e) {
      Error dafny_error = Error.create_KMSInternalException(
        WrappersInterop.CreateStringSome(CharacterSequence(e.getMessage()))
      );
      return CreateFailureOfError(dafny_error);
    }
  }

  public static Wrappers_Compile.Option<Boolean> RegionMatch(
    final IKMSClient client,
    final DafnySequence<? extends Character> region
  ) {
    // We should never be passing anything other than Shim as the 'client'.
    // If this cast fails, that indicates that there is something wrong with
    // our code generation.
    Shim shim = (Shim) client;

    // If the client was created externally we
    // have no way to determine what region it is
    // configured with.
    if (shim.region() == null) {
      return WrappersInterop.CreateBooleanNone();
    }

    // Otherwise we kept record of the region
    // when we created the client.
    String shimRegion = shim.region();
    String regionStr = String(region);
    return WrappersInterop.CreateBooleanSome(regionStr.equals(shimRegion));
  }

  private static String UserAgentSuffix() {
    final DafnySequence<? extends Character> runtime =
      software.amazon.smithy.dafny.conversion.ToDafny.Simple.CharacterSequence(
        "Java"
      );
    return new String(
      (char[]) DafnyUserAgentSuffix(runtime).toArray().unwrap()
    );
  }
}
