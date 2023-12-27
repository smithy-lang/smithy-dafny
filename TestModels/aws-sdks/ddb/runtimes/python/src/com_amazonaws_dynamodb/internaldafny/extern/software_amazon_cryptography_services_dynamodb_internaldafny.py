import module_
from Wrappers import Option_None, Option_Some
from com_amazonaws_dynamodb.smithygenerated.com_amazonaws_dynamodb.shim import DynamoDBClientShim
from com_amazonaws_dynamodb.internaldafny.generated.software_amazon_cryptography_services_dynamodb_internaldafny import *
import com_amazonaws_dynamodb.internaldafny.generated.software_amazon_cryptography_services_dynamodb_internaldafny
import _dafny

import boto3
from botocore.config import Config

class default__(com_amazonaws_dynamodb.internaldafny.generated.software_amazon_cryptography_services_dynamodb_internaldafny.default__):
    @staticmethod
    def DynamoDBClient(region=None):
        if region is not None:
            boto_config = Config(
                region_name=region
            )
            impl = boto3.client("dynamodb", config=boto_config)
        else:
            impl = boto3.client("dynamodb")
            region = boto3.session.Session().region_name
        wrapped_client = DynamoDBClientShim(impl, region)
        return Wrappers.Result_Success(wrapped_client)
    
    @staticmethod
    def DDBClientForRegion(region: _dafny.Seq):
        return default__.DynamoDBClient(_dafny.string_of(region))

    @staticmethod
    def RegionMatch(client, region):
        # We should never be passing anything other than Shim as the 'client'.
        # If this assertion fails, that indicates that there is something wrong with
        # our code generation.
        try:
            assert isinstance(client, DynamoDBClientShim)
        except assertionError:
            raise TypeError("Client provided to RegionMatch is not a DynamoDBClientShim: " + client)

        # Since client is a DynamoDBClientShim, we can reach into its _impl, which is a boto3 client
        client_region_name = client._impl.meta.region_name
        return Option_Some(region.VerbatimString(False) == client_region_name)

import software_amazon_cryptography_services_dynamodb_internaldafny
software_amazon_cryptography_services_dynamodb_internaldafny.default__ = default__
com_amazonaws_dynamodb.internaldafny.generated.software_amazon_cryptography_services_dynamodb_internaldafny.default__ = default__
com_amazonaws_dynamodb.internaldafny.generated.software_amazon_cryptography_services_dynamodb_internaldafny.DynamoDBClient = default__.DynamoDBClient
com_amazonaws_dynamodb.internaldafny.generated.software_amazon_cryptography_services_dynamodb_internaldafny.DDBClientForRegion = default__.DDBClientForRegion