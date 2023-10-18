import module_
from Wrappers import Option_None, Option_Some
from com_amazonaws_kms.smithygenerated.shim import TrentServiceShim
from com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny import *
import com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny

import boto3
# from botocore.config import Config

class default__(com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny.default__):
    @staticmethod
    def KMSClient():
        impl = boto3.client("kms")
        wrapped_client = TrentServiceShim(impl)
        return Wrappers.Result_Success(wrapped_client)

    # TODO: Generate Shim that takes in a region
    # I think this would be needed for DBESDK.
    # def KMSClient(region):
    #     boto_config = Config(
    #         region_name = region
    #     )
    #     impl = boto3.client("kms", config=boto_config)
    #     wrapped_client = TrentServiceShim(impl, region)
    #     return Wrappers.Result_Success(wrapped_client)

    def RegionMatch(client, region):
        # We should never be passing anything other than Shim as the 'client'.
        # If this assertion fails, that indicates that there is something wrong with
        # our code generation.
        try:
            assert isinstance(client, TrentServiceShim)
        except AssertionError:
            raise TypeError("Client provided to RegionMatch is not a Shim: " + client)

        # Since client is a TrentServiceShim, we can reach into its _impl, which is a boto3 client
        client_region_name = client._impl.meta.region_name
        return Option_Some(region.VerbatimString(False) == client_region_name)

com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny.default__ = default__
com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny.TrentServiceClient = default__.KMSClient