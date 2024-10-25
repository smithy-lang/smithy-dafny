import boto3
import _dafny

from botocore.config import Config
from boto3.session import Session

from smithy_dafny_standard_library.internaldafny.generated.Wrappers import Option_Some
from com_amazonaws_s3.smithygenerated.com_amazonaws_s3.shim import AmazonS3Shim
from com_amazonaws_s3.internaldafny.generated.Com_Amazonaws_S3 import *
import com_amazonaws_s3.internaldafny.generated.Com_Amazonaws_S3


# Persist this across calls; this doesn't change
available_aws_regions: list[str] = None

def get_available_aws_regions():
    global available_aws_regions
    if available_aws_regions is not None:
        return available_aws_regions
    available_aws_regions = Session().get_available_regions("s3")
    return available_aws_regions

class default__(com_amazonaws_s3.internaldafny.generated.Com_Amazonaws_S3.default__):
    @staticmethod
    def S3Client(boto_client = None, region = None):
        if boto_client is None:
            if region is not None and region in get_available_aws_regions():
                boto_config = Config(
                    region_name=region
                )
                boto_client = boto3.client("s3", config=boto_config)
            else:
                # If no region is provided,
                # boto_client will use the default region provided by boto3
                boto_client = boto3.client("s3")
                region = boto_client.meta.region_name
        wrapped_client = AmazonS3Shim(boto_client, region)
        return Wrappers.Result_Success(wrapped_client)
    
    @staticmethod
    def S3ClientForRegion(region: _dafny.Seq):
        region_string = _dafny.string_of(region)
        return default__.s3Client(region=region_string)

    @staticmethod
    def RegionMatch(client, region):
        # We should never be passing anything other than Shim as the 'client'.
        # If this assertion fails, that indicates that there is something wrong with
        # our code generation.
        try:
            assert isinstance(client, AmazonS3Shim)
        except AssertionError:
            raise TypeError("Client provided to RegionMatch is not a s3ClientShim: " + client)

        # Since client is a s3ClientShim, we can reach into its _impl, which is a boto3 client,
        # then into the client's .meta.region_name attribute
        client_region_name = client._impl.meta.region_name
        return Option_Some(region.VerbatimString(False) == client_region_name)

com_amazonaws_s3.internaldafny.generated.Com_Amazonaws_S3.default__ = default__
