import module_
from Wrappers import Option_None, Option_Some
from com_amazonaws_kms.smithygenerated.shim import KMSClientShim
from com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny import *
import com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny

import boto3
from botocore.config import Config

class default__(com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny.default__):
    @staticmethod
    def KMSClient(region=None):
        if region is not None:
            boto_config = Config(
                region_name=region
            )
            impl = boto3.client("kms", config=boto_config)
        else:
            impl = boto3.client("kms")
            region = boto3.session.Session().region_name
        wrapped_client = KMSClientShim(impl, region)
        return Wrappers.Result_Success(wrapped_client)

    @staticmethod
    def RegionMatch(client, region):
        # We should never be passing anything other than Shim as the 'client'.
        # If this assertion fails, that indicates that there is something wrong with
        # our code generation.
        try:
            assert isinstance(client, KMSClientShim)
        except AssertionError:
            raise TypeError("Client provided to RegionMatch is not a KMSClientShim: " + client)

        # Since client is a TrentServiceShim, we can reach into its _impl, which is a boto3 client
        client_region_name = client._impl.meta.region_name
        return Option_Some(region.VerbatimString(False) == client_region_name)

com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny.default__ = default__
com_amazonaws_kms.internaldafny.generated.software_amazon_cryptography_services_kms_internaldafny.TrentServiceClient = default__.KMSClient