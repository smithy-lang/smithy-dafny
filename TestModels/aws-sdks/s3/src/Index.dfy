// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/ComAmazonawsS3Types.dfy"

module {:extern "software.amazon.cryptography.services.s3.internaldafny" } Com.Amazonaws.S3 refines AbstractComAmazonawsS3Service {
    function method DefaultS3ClientConfigType() : S3ClientConfigType {
        S3ClientConfigType
    }

    function method {:extern "RegionMatch"} RegionMatch(
      client: IS3Client,
      region: string
    ): Option<bool>
}
