import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Wrappers
import StandardLibrary_mUInt
import StandardLibrary
import UTF8

assert "software_amazon_cryptography_services_kms_internaldafny_types" == __name__
software_amazon_cryptography_services_kms_internaldafny_types = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsValid__AliasNameType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (256))

    @staticmethod
    def IsValid__ArnType(x):
        return ((20) <= (len(x))) and ((len(x)) <= (2048))

    @staticmethod
    def IsValid__CiphertextType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (6144))

    @staticmethod
    def IsValid__CloudHsmClusterIdType(x):
        return ((19) <= (len(x))) and ((len(x)) <= (24))

    @staticmethod
    def IsValid__CustomKeyStoreIdType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (64))

    @staticmethod
    def IsValid__CustomKeyStoreNameType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (256))

    @staticmethod
    def IsValid__DescriptionType(x):
        return ((0) <= (len(x))) and ((len(x)) <= (8192))

    @staticmethod
    def IsValid__GrantIdType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (128))

    @staticmethod
    def IsValid__GrantNameType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (256))

    @staticmethod
    def IsValid__GrantTokenList(x):
        return ((0) <= (len(x))) and ((len(x)) <= (10))

    @staticmethod
    def IsValid__GrantTokenType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (8192))

    @staticmethod
    def IsValid__KeyIdType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (2048))

    @staticmethod
    def IsValid__KeyStorePasswordType(x):
        return ((7) <= (len(x))) and ((len(x)) <= (32))

    @staticmethod
    def IsValid__LimitType(x):
        return ((1) <= (x)) and ((x) <= (1000))

    @staticmethod
    def IsValid__MarkerType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (1024))

    @staticmethod
    def IsValid__NumberOfBytesType(x):
        return ((1) <= (x)) and ((x) <= (1024))

    @staticmethod
    def IsValid__PendingWindowInDaysType(x):
        return ((1) <= (x)) and ((x) <= (365))

    @staticmethod
    def IsValid__PlaintextType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (4096))

    @staticmethod
    def IsValid__PolicyNameType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (128))

    @staticmethod
    def IsValid__PolicyType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (131072))

    @staticmethod
    def IsValid__PrincipalIdType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (256))

    @staticmethod
    def IsValid__PublicKeyType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (8192))

    @staticmethod
    def IsValid__RegionType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (32))

    @staticmethod
    def IsValid__TagKeyType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (128))

    @staticmethod
    def IsValid__TagValueType(x):
        return ((0) <= (len(x))) and ((len(x)) <= (256))

    @staticmethod
    def IsValid__TrustAnchorCertificateType(x):
        return ((1) <= (len(x))) and ((len(x)) <= (5000))


class DafnyCallEvent:
    @classmethod
    def default(cls, default_I, default_O):
        return lambda: DafnyCallEvent_DafnyCallEvent(default_I(), default_O())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DafnyCallEvent(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DafnyCallEvent_DafnyCallEvent)

class DafnyCallEvent_DafnyCallEvent(DafnyCallEvent, NamedTuple('DafnyCallEvent', [('input', Any), ('output', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DafnyCallEvent.DafnyCallEvent({_dafny.string_of(self.input)}, {_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DafnyCallEvent_DafnyCallEvent) and self.input == __o.input and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class AlgorithmSpec:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [AlgorithmSpec_RSAES__PKCS1__V1__5(), AlgorithmSpec_RSAES__OAEP__SHA__1(), AlgorithmSpec_RSAES__OAEP__SHA__256()]
    @classmethod
    def default(cls, ):
        return lambda: AlgorithmSpec_RSAES__PKCS1__V1__5()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_RSAES__PKCS1__V1__5(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.AlgorithmSpec_RSAES__PKCS1__V1__5)
    @property
    def is_RSAES__OAEP__SHA__1(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.AlgorithmSpec_RSAES__OAEP__SHA__1)
    @property
    def is_RSAES__OAEP__SHA__256(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.AlgorithmSpec_RSAES__OAEP__SHA__256)

class AlgorithmSpec_RSAES__PKCS1__V1__5(AlgorithmSpec, NamedTuple('RSAES__PKCS1__V1__5', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.AlgorithmSpec.RSAES_PKCS1_V1_5'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.AlgorithmSpec_RSAES__PKCS1__V1__5)
    def __hash__(self) -> int:
        return super().__hash__()

class AlgorithmSpec_RSAES__OAEP__SHA__1(AlgorithmSpec, NamedTuple('RSAES__OAEP__SHA__1', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.AlgorithmSpec.RSAES_OAEP_SHA_1'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.AlgorithmSpec_RSAES__OAEP__SHA__1)
    def __hash__(self) -> int:
        return super().__hash__()

class AlgorithmSpec_RSAES__OAEP__SHA__256(AlgorithmSpec, NamedTuple('RSAES__OAEP__SHA__256', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.AlgorithmSpec.RSAES_OAEP_SHA_256'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.AlgorithmSpec_RSAES__OAEP__SHA__256)
    def __hash__(self) -> int:
        return super().__hash__()


class AliasListEntry:
    @classmethod
    def default(cls, ):
        return lambda: AliasListEntry_AliasListEntry(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_AliasListEntry(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.AliasListEntry_AliasListEntry)

class AliasListEntry_AliasListEntry(AliasListEntry, NamedTuple('AliasListEntry', [('AliasName', Any), ('AliasArn', Any), ('TargetKeyId', Any), ('CreationDate', Any), ('LastUpdatedDate', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.AliasListEntry.AliasListEntry({_dafny.string_of(self.AliasName)}, {_dafny.string_of(self.AliasArn)}, {_dafny.string_of(self.TargetKeyId)}, {_dafny.string_of(self.CreationDate)}, {_dafny.string_of(self.LastUpdatedDate)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.AliasListEntry_AliasListEntry) and self.AliasName == __o.AliasName and self.AliasArn == __o.AliasArn and self.TargetKeyId == __o.TargetKeyId and self.CreationDate == __o.CreationDate and self.LastUpdatedDate == __o.LastUpdatedDate
    def __hash__(self) -> int:
        return super().__hash__()


class AliasNameType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class ArnType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class CancelKeyDeletionRequest:
    @classmethod
    def default(cls, ):
        return lambda: CancelKeyDeletionRequest_CancelKeyDeletionRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CancelKeyDeletionRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CancelKeyDeletionRequest_CancelKeyDeletionRequest)

class CancelKeyDeletionRequest_CancelKeyDeletionRequest(CancelKeyDeletionRequest, NamedTuple('CancelKeyDeletionRequest', [('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CancelKeyDeletionRequest.CancelKeyDeletionRequest({_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CancelKeyDeletionRequest_CancelKeyDeletionRequest) and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class CancelKeyDeletionResponse:
    @classmethod
    def default(cls, ):
        return lambda: CancelKeyDeletionResponse_CancelKeyDeletionResponse(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CancelKeyDeletionResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CancelKeyDeletionResponse_CancelKeyDeletionResponse)

class CancelKeyDeletionResponse_CancelKeyDeletionResponse(CancelKeyDeletionResponse, NamedTuple('CancelKeyDeletionResponse', [('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CancelKeyDeletionResponse.CancelKeyDeletionResponse({_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CancelKeyDeletionResponse_CancelKeyDeletionResponse) and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class CiphertextType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class CloudHsmClusterIdType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class ConnectCustomKeyStoreRequest:
    @classmethod
    def default(cls, ):
        return lambda: ConnectCustomKeyStoreRequest_ConnectCustomKeyStoreRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ConnectCustomKeyStoreRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectCustomKeyStoreRequest_ConnectCustomKeyStoreRequest)

class ConnectCustomKeyStoreRequest_ConnectCustomKeyStoreRequest(ConnectCustomKeyStoreRequest, NamedTuple('ConnectCustomKeyStoreRequest', [('CustomKeyStoreId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectCustomKeyStoreRequest.ConnectCustomKeyStoreRequest({_dafny.string_of(self.CustomKeyStoreId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectCustomKeyStoreRequest_ConnectCustomKeyStoreRequest) and self.CustomKeyStoreId == __o.CustomKeyStoreId
    def __hash__(self) -> int:
        return super().__hash__()


class ConnectCustomKeyStoreResponse:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [ConnectCustomKeyStoreResponse_ConnectCustomKeyStoreResponse()]
    @classmethod
    def default(cls, ):
        return lambda: ConnectCustomKeyStoreResponse_ConnectCustomKeyStoreResponse()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ConnectCustomKeyStoreResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectCustomKeyStoreResponse_ConnectCustomKeyStoreResponse)

class ConnectCustomKeyStoreResponse_ConnectCustomKeyStoreResponse(ConnectCustomKeyStoreResponse, NamedTuple('ConnectCustomKeyStoreResponse', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectCustomKeyStoreResponse.ConnectCustomKeyStoreResponse'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectCustomKeyStoreResponse_ConnectCustomKeyStoreResponse)
    def __hash__(self) -> int:
        return super().__hash__()


class ConnectionErrorCodeType:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [ConnectionErrorCodeType_INVALID__CREDENTIALS(), ConnectionErrorCodeType_CLUSTER__NOT__FOUND(), ConnectionErrorCodeType_NETWORK__ERRORS(), ConnectionErrorCodeType_INTERNAL__ERROR(), ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS(), ConnectionErrorCodeType_USER__LOCKED__OUT(), ConnectionErrorCodeType_USER__NOT__FOUND(), ConnectionErrorCodeType_USER__LOGGED__IN(), ConnectionErrorCodeType_SUBNET__NOT__FOUND()]
    @classmethod
    def default(cls, ):
        return lambda: ConnectionErrorCodeType_INVALID__CREDENTIALS()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_INVALID__CREDENTIALS(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_INVALID__CREDENTIALS)
    @property
    def is_CLUSTER__NOT__FOUND(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_CLUSTER__NOT__FOUND)
    @property
    def is_NETWORK__ERRORS(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_NETWORK__ERRORS)
    @property
    def is_INTERNAL__ERROR(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_INTERNAL__ERROR)
    @property
    def is_INSUFFICIENT__CLOUDHSM__HSMS(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS)
    @property
    def is_USER__LOCKED__OUT(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_USER__LOCKED__OUT)
    @property
    def is_USER__NOT__FOUND(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_USER__NOT__FOUND)
    @property
    def is_USER__LOGGED__IN(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_USER__LOGGED__IN)
    @property
    def is_SUBNET__NOT__FOUND(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_SUBNET__NOT__FOUND)

class ConnectionErrorCodeType_INVALID__CREDENTIALS(ConnectionErrorCodeType, NamedTuple('INVALID__CREDENTIALS', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionErrorCodeType.INVALID_CREDENTIALS'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_INVALID__CREDENTIALS)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionErrorCodeType_CLUSTER__NOT__FOUND(ConnectionErrorCodeType, NamedTuple('CLUSTER__NOT__FOUND', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionErrorCodeType.CLUSTER_NOT_FOUND'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_CLUSTER__NOT__FOUND)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionErrorCodeType_NETWORK__ERRORS(ConnectionErrorCodeType, NamedTuple('NETWORK__ERRORS', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionErrorCodeType.NETWORK_ERRORS'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_NETWORK__ERRORS)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionErrorCodeType_INTERNAL__ERROR(ConnectionErrorCodeType, NamedTuple('INTERNAL__ERROR', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionErrorCodeType.INTERNAL_ERROR'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_INTERNAL__ERROR)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS(ConnectionErrorCodeType, NamedTuple('INSUFFICIENT__CLOUDHSM__HSMS', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionErrorCodeType.INSUFFICIENT_CLOUDHSM_HSMS'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_INSUFFICIENT__CLOUDHSM__HSMS)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionErrorCodeType_USER__LOCKED__OUT(ConnectionErrorCodeType, NamedTuple('USER__LOCKED__OUT', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionErrorCodeType.USER_LOCKED_OUT'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_USER__LOCKED__OUT)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionErrorCodeType_USER__NOT__FOUND(ConnectionErrorCodeType, NamedTuple('USER__NOT__FOUND', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionErrorCodeType.USER_NOT_FOUND'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_USER__NOT__FOUND)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionErrorCodeType_USER__LOGGED__IN(ConnectionErrorCodeType, NamedTuple('USER__LOGGED__IN', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionErrorCodeType.USER_LOGGED_IN'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_USER__LOGGED__IN)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionErrorCodeType_SUBNET__NOT__FOUND(ConnectionErrorCodeType, NamedTuple('SUBNET__NOT__FOUND', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionErrorCodeType.SUBNET_NOT_FOUND'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionErrorCodeType_SUBNET__NOT__FOUND)
    def __hash__(self) -> int:
        return super().__hash__()


class ConnectionStateType:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [ConnectionStateType_CONNECTED(), ConnectionStateType_CONNECTING(), ConnectionStateType_FAILED(), ConnectionStateType_DISCONNECTED(), ConnectionStateType_DISCONNECTING()]
    @classmethod
    def default(cls, ):
        return lambda: ConnectionStateType_CONNECTED()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CONNECTED(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_CONNECTED)
    @property
    def is_CONNECTING(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_CONNECTING)
    @property
    def is_FAILED(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_FAILED)
    @property
    def is_DISCONNECTED(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_DISCONNECTED)
    @property
    def is_DISCONNECTING(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_DISCONNECTING)

class ConnectionStateType_CONNECTED(ConnectionStateType, NamedTuple('CONNECTED', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionStateType.CONNECTED'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_CONNECTED)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionStateType_CONNECTING(ConnectionStateType, NamedTuple('CONNECTING', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionStateType.CONNECTING'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_CONNECTING)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionStateType_FAILED(ConnectionStateType, NamedTuple('FAILED', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionStateType.FAILED'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_FAILED)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionStateType_DISCONNECTED(ConnectionStateType, NamedTuple('DISCONNECTED', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionStateType.DISCONNECTED'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_DISCONNECTED)
    def __hash__(self) -> int:
        return super().__hash__()

class ConnectionStateType_DISCONNECTING(ConnectionStateType, NamedTuple('DISCONNECTING', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ConnectionStateType.DISCONNECTING'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ConnectionStateType_DISCONNECTING)
    def __hash__(self) -> int:
        return super().__hash__()


class CreateAliasRequest:
    @classmethod
    def default(cls, ):
        return lambda: CreateAliasRequest_CreateAliasRequest(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CreateAliasRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CreateAliasRequest_CreateAliasRequest)

class CreateAliasRequest_CreateAliasRequest(CreateAliasRequest, NamedTuple('CreateAliasRequest', [('AliasName', Any), ('TargetKeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CreateAliasRequest.CreateAliasRequest({_dafny.string_of(self.AliasName)}, {_dafny.string_of(self.TargetKeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CreateAliasRequest_CreateAliasRequest) and self.AliasName == __o.AliasName and self.TargetKeyId == __o.TargetKeyId
    def __hash__(self) -> int:
        return super().__hash__()


class CreateCustomKeyStoreRequest:
    @classmethod
    def default(cls, ):
        return lambda: CreateCustomKeyStoreRequest_CreateCustomKeyStoreRequest(_dafny.Seq({}), _dafny.Seq({}), _dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CreateCustomKeyStoreRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CreateCustomKeyStoreRequest_CreateCustomKeyStoreRequest)

class CreateCustomKeyStoreRequest_CreateCustomKeyStoreRequest(CreateCustomKeyStoreRequest, NamedTuple('CreateCustomKeyStoreRequest', [('CustomKeyStoreName', Any), ('CloudHsmClusterId', Any), ('TrustAnchorCertificate', Any), ('KeyStorePassword', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CreateCustomKeyStoreRequest.CreateCustomKeyStoreRequest({_dafny.string_of(self.CustomKeyStoreName)}, {_dafny.string_of(self.CloudHsmClusterId)}, {_dafny.string_of(self.TrustAnchorCertificate)}, {_dafny.string_of(self.KeyStorePassword)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CreateCustomKeyStoreRequest_CreateCustomKeyStoreRequest) and self.CustomKeyStoreName == __o.CustomKeyStoreName and self.CloudHsmClusterId == __o.CloudHsmClusterId and self.TrustAnchorCertificate == __o.TrustAnchorCertificate and self.KeyStorePassword == __o.KeyStorePassword
    def __hash__(self) -> int:
        return super().__hash__()


class CreateCustomKeyStoreResponse:
    @classmethod
    def default(cls, ):
        return lambda: CreateCustomKeyStoreResponse_CreateCustomKeyStoreResponse(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CreateCustomKeyStoreResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CreateCustomKeyStoreResponse_CreateCustomKeyStoreResponse)

class CreateCustomKeyStoreResponse_CreateCustomKeyStoreResponse(CreateCustomKeyStoreResponse, NamedTuple('CreateCustomKeyStoreResponse', [('CustomKeyStoreId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CreateCustomKeyStoreResponse.CreateCustomKeyStoreResponse({_dafny.string_of(self.CustomKeyStoreId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CreateCustomKeyStoreResponse_CreateCustomKeyStoreResponse) and self.CustomKeyStoreId == __o.CustomKeyStoreId
    def __hash__(self) -> int:
        return super().__hash__()


class CreateGrantRequest:
    @classmethod
    def default(cls, ):
        return lambda: CreateGrantRequest_CreateGrantRequest(_dafny.Seq({}), _dafny.Seq({}), Wrappers.Option.default()(), _dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CreateGrantRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CreateGrantRequest_CreateGrantRequest)

class CreateGrantRequest_CreateGrantRequest(CreateGrantRequest, NamedTuple('CreateGrantRequest', [('KeyId', Any), ('GranteePrincipal', Any), ('RetiringPrincipal', Any), ('Operations', Any), ('Constraints', Any), ('GrantTokens', Any), ('Name', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CreateGrantRequest.CreateGrantRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.GranteePrincipal)}, {_dafny.string_of(self.RetiringPrincipal)}, {_dafny.string_of(self.Operations)}, {_dafny.string_of(self.Constraints)}, {_dafny.string_of(self.GrantTokens)}, {_dafny.string_of(self.Name)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CreateGrantRequest_CreateGrantRequest) and self.KeyId == __o.KeyId and self.GranteePrincipal == __o.GranteePrincipal and self.RetiringPrincipal == __o.RetiringPrincipal and self.Operations == __o.Operations and self.Constraints == __o.Constraints and self.GrantTokens == __o.GrantTokens and self.Name == __o.Name
    def __hash__(self) -> int:
        return super().__hash__()


class CreateGrantResponse:
    @classmethod
    def default(cls, ):
        return lambda: CreateGrantResponse_CreateGrantResponse(Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CreateGrantResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CreateGrantResponse_CreateGrantResponse)

class CreateGrantResponse_CreateGrantResponse(CreateGrantResponse, NamedTuple('CreateGrantResponse', [('GrantToken', Any), ('GrantId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CreateGrantResponse.CreateGrantResponse({_dafny.string_of(self.GrantToken)}, {_dafny.string_of(self.GrantId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CreateGrantResponse_CreateGrantResponse) and self.GrantToken == __o.GrantToken and self.GrantId == __o.GrantId
    def __hash__(self) -> int:
        return super().__hash__()


class CreateKeyRequest:
    @classmethod
    def default(cls, ):
        return lambda: CreateKeyRequest_CreateKeyRequest(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CreateKeyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CreateKeyRequest_CreateKeyRequest)

class CreateKeyRequest_CreateKeyRequest(CreateKeyRequest, NamedTuple('CreateKeyRequest', [('Policy', Any), ('Description', Any), ('KeyUsage', Any), ('CustomerMasterKeySpec', Any), ('KeySpec', Any), ('Origin', Any), ('CustomKeyStoreId', Any), ('BypassPolicyLockoutSafetyCheck', Any), ('Tags', Any), ('MultiRegion', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CreateKeyRequest.CreateKeyRequest({_dafny.string_of(self.Policy)}, {_dafny.string_of(self.Description)}, {_dafny.string_of(self.KeyUsage)}, {_dafny.string_of(self.CustomerMasterKeySpec)}, {_dafny.string_of(self.KeySpec)}, {_dafny.string_of(self.Origin)}, {_dafny.string_of(self.CustomKeyStoreId)}, {_dafny.string_of(self.BypassPolicyLockoutSafetyCheck)}, {_dafny.string_of(self.Tags)}, {_dafny.string_of(self.MultiRegion)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CreateKeyRequest_CreateKeyRequest) and self.Policy == __o.Policy and self.Description == __o.Description and self.KeyUsage == __o.KeyUsage and self.CustomerMasterKeySpec == __o.CustomerMasterKeySpec and self.KeySpec == __o.KeySpec and self.Origin == __o.Origin and self.CustomKeyStoreId == __o.CustomKeyStoreId and self.BypassPolicyLockoutSafetyCheck == __o.BypassPolicyLockoutSafetyCheck and self.Tags == __o.Tags and self.MultiRegion == __o.MultiRegion
    def __hash__(self) -> int:
        return super().__hash__()


class CreateKeyResponse:
    @classmethod
    def default(cls, ):
        return lambda: CreateKeyResponse_CreateKeyResponse(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CreateKeyResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CreateKeyResponse_CreateKeyResponse)

class CreateKeyResponse_CreateKeyResponse(CreateKeyResponse, NamedTuple('CreateKeyResponse', [('KeyMetadata', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CreateKeyResponse.CreateKeyResponse({_dafny.string_of(self.KeyMetadata)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CreateKeyResponse_CreateKeyResponse) and self.KeyMetadata == __o.KeyMetadata
    def __hash__(self) -> int:
        return super().__hash__()


class CustomerMasterKeySpec:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [CustomerMasterKeySpec_RSA__2048(), CustomerMasterKeySpec_RSA__3072(), CustomerMasterKeySpec_RSA__4096(), CustomerMasterKeySpec_ECC__NIST__P256(), CustomerMasterKeySpec_ECC__NIST__P384(), CustomerMasterKeySpec_ECC__NIST__P521(), CustomerMasterKeySpec_ECC__SECG__P256K1(), CustomerMasterKeySpec_SYMMETRIC__DEFAULT()]
    @classmethod
    def default(cls, ):
        return lambda: CustomerMasterKeySpec_RSA__2048()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_RSA__2048(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_RSA__2048)
    @property
    def is_RSA__3072(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_RSA__3072)
    @property
    def is_RSA__4096(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_RSA__4096)
    @property
    def is_ECC__NIST__P256(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_ECC__NIST__P256)
    @property
    def is_ECC__NIST__P384(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_ECC__NIST__P384)
    @property
    def is_ECC__NIST__P521(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_ECC__NIST__P521)
    @property
    def is_ECC__SECG__P256K1(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_ECC__SECG__P256K1)
    @property
    def is_SYMMETRIC__DEFAULT(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_SYMMETRIC__DEFAULT)

class CustomerMasterKeySpec_RSA__2048(CustomerMasterKeySpec, NamedTuple('RSA__2048', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CustomerMasterKeySpec.RSA_2048'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_RSA__2048)
    def __hash__(self) -> int:
        return super().__hash__()

class CustomerMasterKeySpec_RSA__3072(CustomerMasterKeySpec, NamedTuple('RSA__3072', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CustomerMasterKeySpec.RSA_3072'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_RSA__3072)
    def __hash__(self) -> int:
        return super().__hash__()

class CustomerMasterKeySpec_RSA__4096(CustomerMasterKeySpec, NamedTuple('RSA__4096', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CustomerMasterKeySpec.RSA_4096'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_RSA__4096)
    def __hash__(self) -> int:
        return super().__hash__()

class CustomerMasterKeySpec_ECC__NIST__P256(CustomerMasterKeySpec, NamedTuple('ECC__NIST__P256', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CustomerMasterKeySpec.ECC_NIST_P256'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_ECC__NIST__P256)
    def __hash__(self) -> int:
        return super().__hash__()

class CustomerMasterKeySpec_ECC__NIST__P384(CustomerMasterKeySpec, NamedTuple('ECC__NIST__P384', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CustomerMasterKeySpec.ECC_NIST_P384'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_ECC__NIST__P384)
    def __hash__(self) -> int:
        return super().__hash__()

class CustomerMasterKeySpec_ECC__NIST__P521(CustomerMasterKeySpec, NamedTuple('ECC__NIST__P521', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CustomerMasterKeySpec.ECC_NIST_P521'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_ECC__NIST__P521)
    def __hash__(self) -> int:
        return super().__hash__()

class CustomerMasterKeySpec_ECC__SECG__P256K1(CustomerMasterKeySpec, NamedTuple('ECC__SECG__P256K1', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CustomerMasterKeySpec.ECC_SECG_P256K1'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_ECC__SECG__P256K1)
    def __hash__(self) -> int:
        return super().__hash__()

class CustomerMasterKeySpec_SYMMETRIC__DEFAULT(CustomerMasterKeySpec, NamedTuple('SYMMETRIC__DEFAULT', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CustomerMasterKeySpec.SYMMETRIC_DEFAULT'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CustomerMasterKeySpec_SYMMETRIC__DEFAULT)
    def __hash__(self) -> int:
        return super().__hash__()


class CustomKeyStoreIdType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class CustomKeyStoreNameType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class CustomKeyStoresListEntry:
    @classmethod
    def default(cls, ):
        return lambda: CustomKeyStoresListEntry_CustomKeyStoresListEntry(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CustomKeyStoresListEntry(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.CustomKeyStoresListEntry_CustomKeyStoresListEntry)

class CustomKeyStoresListEntry_CustomKeyStoresListEntry(CustomKeyStoresListEntry, NamedTuple('CustomKeyStoresListEntry', [('CustomKeyStoreId', Any), ('CustomKeyStoreName', Any), ('CloudHsmClusterId', Any), ('TrustAnchorCertificate', Any), ('ConnectionState', Any), ('ConnectionErrorCode', Any), ('CreationDate', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.CustomKeyStoresListEntry.CustomKeyStoresListEntry({_dafny.string_of(self.CustomKeyStoreId)}, {_dafny.string_of(self.CustomKeyStoreName)}, {_dafny.string_of(self.CloudHsmClusterId)}, {_dafny.string_of(self.TrustAnchorCertificate)}, {_dafny.string_of(self.ConnectionState)}, {_dafny.string_of(self.ConnectionErrorCode)}, {_dafny.string_of(self.CreationDate)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.CustomKeyStoresListEntry_CustomKeyStoresListEntry) and self.CustomKeyStoreId == __o.CustomKeyStoreId and self.CustomKeyStoreName == __o.CustomKeyStoreName and self.CloudHsmClusterId == __o.CloudHsmClusterId and self.TrustAnchorCertificate == __o.TrustAnchorCertificate and self.ConnectionState == __o.ConnectionState and self.ConnectionErrorCode == __o.ConnectionErrorCode and self.CreationDate == __o.CreationDate
    def __hash__(self) -> int:
        return super().__hash__()


class DataKeyPairSpec:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [DataKeyPairSpec_RSA__2048(), DataKeyPairSpec_RSA__3072(), DataKeyPairSpec_RSA__4096(), DataKeyPairSpec_ECC__NIST__P256(), DataKeyPairSpec_ECC__NIST__P384(), DataKeyPairSpec_ECC__NIST__P521(), DataKeyPairSpec_ECC__SECG__P256K1()]
    @classmethod
    def default(cls, ):
        return lambda: DataKeyPairSpec_RSA__2048()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_RSA__2048(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_RSA__2048)
    @property
    def is_RSA__3072(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_RSA__3072)
    @property
    def is_RSA__4096(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_RSA__4096)
    @property
    def is_ECC__NIST__P256(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_ECC__NIST__P256)
    @property
    def is_ECC__NIST__P384(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_ECC__NIST__P384)
    @property
    def is_ECC__NIST__P521(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_ECC__NIST__P521)
    @property
    def is_ECC__SECG__P256K1(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_ECC__SECG__P256K1)

class DataKeyPairSpec_RSA__2048(DataKeyPairSpec, NamedTuple('RSA__2048', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DataKeyPairSpec.RSA_2048'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_RSA__2048)
    def __hash__(self) -> int:
        return super().__hash__()

class DataKeyPairSpec_RSA__3072(DataKeyPairSpec, NamedTuple('RSA__3072', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DataKeyPairSpec.RSA_3072'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_RSA__3072)
    def __hash__(self) -> int:
        return super().__hash__()

class DataKeyPairSpec_RSA__4096(DataKeyPairSpec, NamedTuple('RSA__4096', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DataKeyPairSpec.RSA_4096'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_RSA__4096)
    def __hash__(self) -> int:
        return super().__hash__()

class DataKeyPairSpec_ECC__NIST__P256(DataKeyPairSpec, NamedTuple('ECC__NIST__P256', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DataKeyPairSpec.ECC_NIST_P256'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_ECC__NIST__P256)
    def __hash__(self) -> int:
        return super().__hash__()

class DataKeyPairSpec_ECC__NIST__P384(DataKeyPairSpec, NamedTuple('ECC__NIST__P384', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DataKeyPairSpec.ECC_NIST_P384'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_ECC__NIST__P384)
    def __hash__(self) -> int:
        return super().__hash__()

class DataKeyPairSpec_ECC__NIST__P521(DataKeyPairSpec, NamedTuple('ECC__NIST__P521', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DataKeyPairSpec.ECC_NIST_P521'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_ECC__NIST__P521)
    def __hash__(self) -> int:
        return super().__hash__()

class DataKeyPairSpec_ECC__SECG__P256K1(DataKeyPairSpec, NamedTuple('ECC__SECG__P256K1', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DataKeyPairSpec.ECC_SECG_P256K1'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec_ECC__SECG__P256K1)
    def __hash__(self) -> int:
        return super().__hash__()


class DataKeySpec:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [DataKeySpec_AES__256(), DataKeySpec_AES__128()]
    @classmethod
    def default(cls, ):
        return lambda: DataKeySpec_AES__256()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_AES__256(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DataKeySpec_AES__256)
    @property
    def is_AES__128(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DataKeySpec_AES__128)

class DataKeySpec_AES__256(DataKeySpec, NamedTuple('AES__256', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DataKeySpec.AES_256'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DataKeySpec_AES__256)
    def __hash__(self) -> int:
        return super().__hash__()

class DataKeySpec_AES__128(DataKeySpec, NamedTuple('AES__128', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DataKeySpec.AES_128'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DataKeySpec_AES__128)
    def __hash__(self) -> int:
        return super().__hash__()


class DecryptRequest:
    @classmethod
    def default(cls, ):
        return lambda: DecryptRequest_DecryptRequest(_dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DecryptRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DecryptRequest_DecryptRequest)

class DecryptRequest_DecryptRequest(DecryptRequest, NamedTuple('DecryptRequest', [('CiphertextBlob', Any), ('EncryptionContext', Any), ('GrantTokens', Any), ('KeyId', Any), ('EncryptionAlgorithm', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DecryptRequest.DecryptRequest({_dafny.string_of(self.CiphertextBlob)}, {_dafny.string_of(self.EncryptionContext)}, {_dafny.string_of(self.GrantTokens)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.EncryptionAlgorithm)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DecryptRequest_DecryptRequest) and self.CiphertextBlob == __o.CiphertextBlob and self.EncryptionContext == __o.EncryptionContext and self.GrantTokens == __o.GrantTokens and self.KeyId == __o.KeyId and self.EncryptionAlgorithm == __o.EncryptionAlgorithm
    def __hash__(self) -> int:
        return super().__hash__()


class DecryptResponse:
    @classmethod
    def default(cls, ):
        return lambda: DecryptResponse_DecryptResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DecryptResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DecryptResponse_DecryptResponse)

class DecryptResponse_DecryptResponse(DecryptResponse, NamedTuple('DecryptResponse', [('KeyId', Any), ('Plaintext', Any), ('EncryptionAlgorithm', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DecryptResponse.DecryptResponse({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Plaintext)}, {_dafny.string_of(self.EncryptionAlgorithm)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DecryptResponse_DecryptResponse) and self.KeyId == __o.KeyId and self.Plaintext == __o.Plaintext and self.EncryptionAlgorithm == __o.EncryptionAlgorithm
    def __hash__(self) -> int:
        return super().__hash__()


class DeleteAliasRequest:
    @classmethod
    def default(cls, ):
        return lambda: DeleteAliasRequest_DeleteAliasRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DeleteAliasRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DeleteAliasRequest_DeleteAliasRequest)

class DeleteAliasRequest_DeleteAliasRequest(DeleteAliasRequest, NamedTuple('DeleteAliasRequest', [('AliasName', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DeleteAliasRequest.DeleteAliasRequest({_dafny.string_of(self.AliasName)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DeleteAliasRequest_DeleteAliasRequest) and self.AliasName == __o.AliasName
    def __hash__(self) -> int:
        return super().__hash__()


class DeleteCustomKeyStoreRequest:
    @classmethod
    def default(cls, ):
        return lambda: DeleteCustomKeyStoreRequest_DeleteCustomKeyStoreRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DeleteCustomKeyStoreRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DeleteCustomKeyStoreRequest_DeleteCustomKeyStoreRequest)

class DeleteCustomKeyStoreRequest_DeleteCustomKeyStoreRequest(DeleteCustomKeyStoreRequest, NamedTuple('DeleteCustomKeyStoreRequest', [('CustomKeyStoreId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DeleteCustomKeyStoreRequest.DeleteCustomKeyStoreRequest({_dafny.string_of(self.CustomKeyStoreId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DeleteCustomKeyStoreRequest_DeleteCustomKeyStoreRequest) and self.CustomKeyStoreId == __o.CustomKeyStoreId
    def __hash__(self) -> int:
        return super().__hash__()


class DeleteCustomKeyStoreResponse:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [DeleteCustomKeyStoreResponse_DeleteCustomKeyStoreResponse()]
    @classmethod
    def default(cls, ):
        return lambda: DeleteCustomKeyStoreResponse_DeleteCustomKeyStoreResponse()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DeleteCustomKeyStoreResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DeleteCustomKeyStoreResponse_DeleteCustomKeyStoreResponse)

class DeleteCustomKeyStoreResponse_DeleteCustomKeyStoreResponse(DeleteCustomKeyStoreResponse, NamedTuple('DeleteCustomKeyStoreResponse', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DeleteCustomKeyStoreResponse.DeleteCustomKeyStoreResponse'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DeleteCustomKeyStoreResponse_DeleteCustomKeyStoreResponse)
    def __hash__(self) -> int:
        return super().__hash__()


class DeleteImportedKeyMaterialRequest:
    @classmethod
    def default(cls, ):
        return lambda: DeleteImportedKeyMaterialRequest_DeleteImportedKeyMaterialRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DeleteImportedKeyMaterialRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DeleteImportedKeyMaterialRequest_DeleteImportedKeyMaterialRequest)

class DeleteImportedKeyMaterialRequest_DeleteImportedKeyMaterialRequest(DeleteImportedKeyMaterialRequest, NamedTuple('DeleteImportedKeyMaterialRequest', [('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DeleteImportedKeyMaterialRequest.DeleteImportedKeyMaterialRequest({_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DeleteImportedKeyMaterialRequest_DeleteImportedKeyMaterialRequest) and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class DescribeCustomKeyStoresRequest:
    @classmethod
    def default(cls, ):
        return lambda: DescribeCustomKeyStoresRequest_DescribeCustomKeyStoresRequest(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DescribeCustomKeyStoresRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DescribeCustomKeyStoresRequest_DescribeCustomKeyStoresRequest)

class DescribeCustomKeyStoresRequest_DescribeCustomKeyStoresRequest(DescribeCustomKeyStoresRequest, NamedTuple('DescribeCustomKeyStoresRequest', [('CustomKeyStoreId', Any), ('CustomKeyStoreName', Any), ('Limit', Any), ('Marker', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DescribeCustomKeyStoresRequest.DescribeCustomKeyStoresRequest({_dafny.string_of(self.CustomKeyStoreId)}, {_dafny.string_of(self.CustomKeyStoreName)}, {_dafny.string_of(self.Limit)}, {_dafny.string_of(self.Marker)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DescribeCustomKeyStoresRequest_DescribeCustomKeyStoresRequest) and self.CustomKeyStoreId == __o.CustomKeyStoreId and self.CustomKeyStoreName == __o.CustomKeyStoreName and self.Limit == __o.Limit and self.Marker == __o.Marker
    def __hash__(self) -> int:
        return super().__hash__()


class DescribeCustomKeyStoresResponse:
    @classmethod
    def default(cls, ):
        return lambda: DescribeCustomKeyStoresResponse_DescribeCustomKeyStoresResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DescribeCustomKeyStoresResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DescribeCustomKeyStoresResponse_DescribeCustomKeyStoresResponse)

class DescribeCustomKeyStoresResponse_DescribeCustomKeyStoresResponse(DescribeCustomKeyStoresResponse, NamedTuple('DescribeCustomKeyStoresResponse', [('CustomKeyStores', Any), ('NextMarker', Any), ('Truncated', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DescribeCustomKeyStoresResponse.DescribeCustomKeyStoresResponse({_dafny.string_of(self.CustomKeyStores)}, {_dafny.string_of(self.NextMarker)}, {_dafny.string_of(self.Truncated)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DescribeCustomKeyStoresResponse_DescribeCustomKeyStoresResponse) and self.CustomKeyStores == __o.CustomKeyStores and self.NextMarker == __o.NextMarker and self.Truncated == __o.Truncated
    def __hash__(self) -> int:
        return super().__hash__()


class DescribeKeyRequest:
    @classmethod
    def default(cls, ):
        return lambda: DescribeKeyRequest_DescribeKeyRequest(_dafny.Seq({}), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DescribeKeyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DescribeKeyRequest_DescribeKeyRequest)

class DescribeKeyRequest_DescribeKeyRequest(DescribeKeyRequest, NamedTuple('DescribeKeyRequest', [('KeyId', Any), ('GrantTokens', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DescribeKeyRequest.DescribeKeyRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.GrantTokens)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DescribeKeyRequest_DescribeKeyRequest) and self.KeyId == __o.KeyId and self.GrantTokens == __o.GrantTokens
    def __hash__(self) -> int:
        return super().__hash__()


class DescribeKeyResponse:
    @classmethod
    def default(cls, ):
        return lambda: DescribeKeyResponse_DescribeKeyResponse(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DescribeKeyResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DescribeKeyResponse_DescribeKeyResponse)

class DescribeKeyResponse_DescribeKeyResponse(DescribeKeyResponse, NamedTuple('DescribeKeyResponse', [('KeyMetadata', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DescribeKeyResponse.DescribeKeyResponse({_dafny.string_of(self.KeyMetadata)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DescribeKeyResponse_DescribeKeyResponse) and self.KeyMetadata == __o.KeyMetadata
    def __hash__(self) -> int:
        return super().__hash__()


class DescriptionType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class DisableKeyRequest:
    @classmethod
    def default(cls, ):
        return lambda: DisableKeyRequest_DisableKeyRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DisableKeyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DisableKeyRequest_DisableKeyRequest)

class DisableKeyRequest_DisableKeyRequest(DisableKeyRequest, NamedTuple('DisableKeyRequest', [('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DisableKeyRequest.DisableKeyRequest({_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DisableKeyRequest_DisableKeyRequest) and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class DisableKeyRotationRequest:
    @classmethod
    def default(cls, ):
        return lambda: DisableKeyRotationRequest_DisableKeyRotationRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DisableKeyRotationRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DisableKeyRotationRequest_DisableKeyRotationRequest)

class DisableKeyRotationRequest_DisableKeyRotationRequest(DisableKeyRotationRequest, NamedTuple('DisableKeyRotationRequest', [('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DisableKeyRotationRequest.DisableKeyRotationRequest({_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DisableKeyRotationRequest_DisableKeyRotationRequest) and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class DisconnectCustomKeyStoreRequest:
    @classmethod
    def default(cls, ):
        return lambda: DisconnectCustomKeyStoreRequest_DisconnectCustomKeyStoreRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DisconnectCustomKeyStoreRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DisconnectCustomKeyStoreRequest_DisconnectCustomKeyStoreRequest)

class DisconnectCustomKeyStoreRequest_DisconnectCustomKeyStoreRequest(DisconnectCustomKeyStoreRequest, NamedTuple('DisconnectCustomKeyStoreRequest', [('CustomKeyStoreId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DisconnectCustomKeyStoreRequest.DisconnectCustomKeyStoreRequest({_dafny.string_of(self.CustomKeyStoreId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DisconnectCustomKeyStoreRequest_DisconnectCustomKeyStoreRequest) and self.CustomKeyStoreId == __o.CustomKeyStoreId
    def __hash__(self) -> int:
        return super().__hash__()


class DisconnectCustomKeyStoreResponse:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [DisconnectCustomKeyStoreResponse_DisconnectCustomKeyStoreResponse()]
    @classmethod
    def default(cls, ):
        return lambda: DisconnectCustomKeyStoreResponse_DisconnectCustomKeyStoreResponse()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DisconnectCustomKeyStoreResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.DisconnectCustomKeyStoreResponse_DisconnectCustomKeyStoreResponse)

class DisconnectCustomKeyStoreResponse_DisconnectCustomKeyStoreResponse(DisconnectCustomKeyStoreResponse, NamedTuple('DisconnectCustomKeyStoreResponse', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.DisconnectCustomKeyStoreResponse.DisconnectCustomKeyStoreResponse'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.DisconnectCustomKeyStoreResponse_DisconnectCustomKeyStoreResponse)
    def __hash__(self) -> int:
        return super().__hash__()


class EnableKeyRequest:
    @classmethod
    def default(cls, ):
        return lambda: EnableKeyRequest_EnableKeyRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_EnableKeyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.EnableKeyRequest_EnableKeyRequest)

class EnableKeyRequest_EnableKeyRequest(EnableKeyRequest, NamedTuple('EnableKeyRequest', [('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.EnableKeyRequest.EnableKeyRequest({_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.EnableKeyRequest_EnableKeyRequest) and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class EnableKeyRotationRequest:
    @classmethod
    def default(cls, ):
        return lambda: EnableKeyRotationRequest_EnableKeyRotationRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_EnableKeyRotationRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.EnableKeyRotationRequest_EnableKeyRotationRequest)

class EnableKeyRotationRequest_EnableKeyRotationRequest(EnableKeyRotationRequest, NamedTuple('EnableKeyRotationRequest', [('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.EnableKeyRotationRequest.EnableKeyRotationRequest({_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.EnableKeyRotationRequest_EnableKeyRotationRequest) and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class EncryptionAlgorithmSpec:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT(), EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1(), EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256()]
    @classmethod
    def default(cls, ):
        return lambda: EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SYMMETRIC__DEFAULT(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT)
    @property
    def is_RSAES__OAEP__SHA__1(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1)
    @property
    def is_RSAES__OAEP__SHA__256(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256)

class EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT(EncryptionAlgorithmSpec, NamedTuple('SYMMETRIC__DEFAULT', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.SYMMETRIC_DEFAULT'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.EncryptionAlgorithmSpec_SYMMETRIC__DEFAULT)
    def __hash__(self) -> int:
        return super().__hash__()

class EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1(EncryptionAlgorithmSpec, NamedTuple('RSAES__OAEP__SHA__1', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_1'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.EncryptionAlgorithmSpec_RSAES__OAEP__SHA__1)
    def __hash__(self) -> int:
        return super().__hash__()

class EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256(EncryptionAlgorithmSpec, NamedTuple('RSAES__OAEP__SHA__256', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.EncryptionAlgorithmSpec.RSAES_OAEP_SHA_256'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.EncryptionAlgorithmSpec_RSAES__OAEP__SHA__256)
    def __hash__(self) -> int:
        return super().__hash__()


class EncryptRequest:
    @classmethod
    def default(cls, ):
        return lambda: EncryptRequest_EncryptRequest(_dafny.Seq({}), _dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_EncryptRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.EncryptRequest_EncryptRequest)

class EncryptRequest_EncryptRequest(EncryptRequest, NamedTuple('EncryptRequest', [('KeyId', Any), ('Plaintext', Any), ('EncryptionContext', Any), ('GrantTokens', Any), ('EncryptionAlgorithm', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.EncryptRequest.EncryptRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Plaintext)}, {_dafny.string_of(self.EncryptionContext)}, {_dafny.string_of(self.GrantTokens)}, {_dafny.string_of(self.EncryptionAlgorithm)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.EncryptRequest_EncryptRequest) and self.KeyId == __o.KeyId and self.Plaintext == __o.Plaintext and self.EncryptionContext == __o.EncryptionContext and self.GrantTokens == __o.GrantTokens and self.EncryptionAlgorithm == __o.EncryptionAlgorithm
    def __hash__(self) -> int:
        return super().__hash__()


class EncryptResponse:
    @classmethod
    def default(cls, ):
        return lambda: EncryptResponse_EncryptResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_EncryptResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.EncryptResponse_EncryptResponse)

class EncryptResponse_EncryptResponse(EncryptResponse, NamedTuple('EncryptResponse', [('CiphertextBlob', Any), ('KeyId', Any), ('EncryptionAlgorithm', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.EncryptResponse.EncryptResponse({_dafny.string_of(self.CiphertextBlob)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.EncryptionAlgorithm)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.EncryptResponse_EncryptResponse) and self.CiphertextBlob == __o.CiphertextBlob and self.KeyId == __o.KeyId and self.EncryptionAlgorithm == __o.EncryptionAlgorithm
    def __hash__(self) -> int:
        return super().__hash__()


class ExpirationModelType:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [ExpirationModelType_KEY__MATERIAL__EXPIRES(), ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE()]
    @classmethod
    def default(cls, ):
        return lambda: ExpirationModelType_KEY__MATERIAL__EXPIRES()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_KEY__MATERIAL__EXPIRES(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ExpirationModelType_KEY__MATERIAL__EXPIRES)
    @property
    def is_KEY__MATERIAL__DOES__NOT__EXPIRE(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE)

class ExpirationModelType_KEY__MATERIAL__EXPIRES(ExpirationModelType, NamedTuple('KEY__MATERIAL__EXPIRES', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ExpirationModelType.KEY_MATERIAL_EXPIRES'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ExpirationModelType_KEY__MATERIAL__EXPIRES)
    def __hash__(self) -> int:
        return super().__hash__()

class ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE(ExpirationModelType, NamedTuple('KEY__MATERIAL__DOES__NOT__EXPIRE', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ExpirationModelType.KEY_MATERIAL_DOES_NOT_EXPIRE'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ExpirationModelType_KEY__MATERIAL__DOES__NOT__EXPIRE)
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateDataKeyPairRequest:
    @classmethod
    def default(cls, ):
        return lambda: GenerateDataKeyPairRequest_GenerateDataKeyPairRequest(Wrappers.Option.default()(), _dafny.Seq({}), software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateDataKeyPairRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyPairRequest_GenerateDataKeyPairRequest)

class GenerateDataKeyPairRequest_GenerateDataKeyPairRequest(GenerateDataKeyPairRequest, NamedTuple('GenerateDataKeyPairRequest', [('EncryptionContext', Any), ('KeyId', Any), ('KeyPairSpec', Any), ('GrantTokens', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateDataKeyPairRequest.GenerateDataKeyPairRequest({_dafny.string_of(self.EncryptionContext)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.KeyPairSpec)}, {_dafny.string_of(self.GrantTokens)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyPairRequest_GenerateDataKeyPairRequest) and self.EncryptionContext == __o.EncryptionContext and self.KeyId == __o.KeyId and self.KeyPairSpec == __o.KeyPairSpec and self.GrantTokens == __o.GrantTokens
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateDataKeyPairResponse:
    @classmethod
    def default(cls, ):
        return lambda: GenerateDataKeyPairResponse_GenerateDataKeyPairResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateDataKeyPairResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyPairResponse_GenerateDataKeyPairResponse)

class GenerateDataKeyPairResponse_GenerateDataKeyPairResponse(GenerateDataKeyPairResponse, NamedTuple('GenerateDataKeyPairResponse', [('PrivateKeyCiphertextBlob', Any), ('PrivateKeyPlaintext', Any), ('PublicKey', Any), ('KeyId', Any), ('KeyPairSpec', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateDataKeyPairResponse.GenerateDataKeyPairResponse({_dafny.string_of(self.PrivateKeyCiphertextBlob)}, {_dafny.string_of(self.PrivateKeyPlaintext)}, {_dafny.string_of(self.PublicKey)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.KeyPairSpec)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyPairResponse_GenerateDataKeyPairResponse) and self.PrivateKeyCiphertextBlob == __o.PrivateKeyCiphertextBlob and self.PrivateKeyPlaintext == __o.PrivateKeyPlaintext and self.PublicKey == __o.PublicKey and self.KeyId == __o.KeyId and self.KeyPairSpec == __o.KeyPairSpec
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateDataKeyPairWithoutPlaintextRequest:
    @classmethod
    def default(cls, ):
        return lambda: GenerateDataKeyPairWithoutPlaintextRequest_GenerateDataKeyPairWithoutPlaintextRequest(Wrappers.Option.default()(), _dafny.Seq({}), software_amazon_cryptography_services_kms_internaldafny_types.DataKeyPairSpec.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateDataKeyPairWithoutPlaintextRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyPairWithoutPlaintextRequest_GenerateDataKeyPairWithoutPlaintextRequest)

class GenerateDataKeyPairWithoutPlaintextRequest_GenerateDataKeyPairWithoutPlaintextRequest(GenerateDataKeyPairWithoutPlaintextRequest, NamedTuple('GenerateDataKeyPairWithoutPlaintextRequest', [('EncryptionContext', Any), ('KeyId', Any), ('KeyPairSpec', Any), ('GrantTokens', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateDataKeyPairWithoutPlaintextRequest.GenerateDataKeyPairWithoutPlaintextRequest({_dafny.string_of(self.EncryptionContext)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.KeyPairSpec)}, {_dafny.string_of(self.GrantTokens)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyPairWithoutPlaintextRequest_GenerateDataKeyPairWithoutPlaintextRequest) and self.EncryptionContext == __o.EncryptionContext and self.KeyId == __o.KeyId and self.KeyPairSpec == __o.KeyPairSpec and self.GrantTokens == __o.GrantTokens
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateDataKeyPairWithoutPlaintextResponse:
    @classmethod
    def default(cls, ):
        return lambda: GenerateDataKeyPairWithoutPlaintextResponse_GenerateDataKeyPairWithoutPlaintextResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateDataKeyPairWithoutPlaintextResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyPairWithoutPlaintextResponse_GenerateDataKeyPairWithoutPlaintextResponse)

class GenerateDataKeyPairWithoutPlaintextResponse_GenerateDataKeyPairWithoutPlaintextResponse(GenerateDataKeyPairWithoutPlaintextResponse, NamedTuple('GenerateDataKeyPairWithoutPlaintextResponse', [('PrivateKeyCiphertextBlob', Any), ('PublicKey', Any), ('KeyId', Any), ('KeyPairSpec', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateDataKeyPairWithoutPlaintextResponse.GenerateDataKeyPairWithoutPlaintextResponse({_dafny.string_of(self.PrivateKeyCiphertextBlob)}, {_dafny.string_of(self.PublicKey)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.KeyPairSpec)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyPairWithoutPlaintextResponse_GenerateDataKeyPairWithoutPlaintextResponse) and self.PrivateKeyCiphertextBlob == __o.PrivateKeyCiphertextBlob and self.PublicKey == __o.PublicKey and self.KeyId == __o.KeyId and self.KeyPairSpec == __o.KeyPairSpec
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateDataKeyRequest:
    @classmethod
    def default(cls, ):
        return lambda: GenerateDataKeyRequest_GenerateDataKeyRequest(_dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateDataKeyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyRequest_GenerateDataKeyRequest)

class GenerateDataKeyRequest_GenerateDataKeyRequest(GenerateDataKeyRequest, NamedTuple('GenerateDataKeyRequest', [('KeyId', Any), ('EncryptionContext', Any), ('NumberOfBytes', Any), ('KeySpec', Any), ('GrantTokens', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateDataKeyRequest.GenerateDataKeyRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.EncryptionContext)}, {_dafny.string_of(self.NumberOfBytes)}, {_dafny.string_of(self.KeySpec)}, {_dafny.string_of(self.GrantTokens)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyRequest_GenerateDataKeyRequest) and self.KeyId == __o.KeyId and self.EncryptionContext == __o.EncryptionContext and self.NumberOfBytes == __o.NumberOfBytes and self.KeySpec == __o.KeySpec and self.GrantTokens == __o.GrantTokens
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateDataKeyResponse:
    @classmethod
    def default(cls, ):
        return lambda: GenerateDataKeyResponse_GenerateDataKeyResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateDataKeyResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyResponse_GenerateDataKeyResponse)

class GenerateDataKeyResponse_GenerateDataKeyResponse(GenerateDataKeyResponse, NamedTuple('GenerateDataKeyResponse', [('CiphertextBlob', Any), ('Plaintext', Any), ('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateDataKeyResponse.GenerateDataKeyResponse({_dafny.string_of(self.CiphertextBlob)}, {_dafny.string_of(self.Plaintext)}, {_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyResponse_GenerateDataKeyResponse) and self.CiphertextBlob == __o.CiphertextBlob and self.Plaintext == __o.Plaintext and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateDataKeyWithoutPlaintextRequest:
    @classmethod
    def default(cls, ):
        return lambda: GenerateDataKeyWithoutPlaintextRequest_GenerateDataKeyWithoutPlaintextRequest(_dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateDataKeyWithoutPlaintextRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyWithoutPlaintextRequest_GenerateDataKeyWithoutPlaintextRequest)

class GenerateDataKeyWithoutPlaintextRequest_GenerateDataKeyWithoutPlaintextRequest(GenerateDataKeyWithoutPlaintextRequest, NamedTuple('GenerateDataKeyWithoutPlaintextRequest', [('KeyId', Any), ('EncryptionContext', Any), ('KeySpec', Any), ('NumberOfBytes', Any), ('GrantTokens', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateDataKeyWithoutPlaintextRequest.GenerateDataKeyWithoutPlaintextRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.EncryptionContext)}, {_dafny.string_of(self.KeySpec)}, {_dafny.string_of(self.NumberOfBytes)}, {_dafny.string_of(self.GrantTokens)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyWithoutPlaintextRequest_GenerateDataKeyWithoutPlaintextRequest) and self.KeyId == __o.KeyId and self.EncryptionContext == __o.EncryptionContext and self.KeySpec == __o.KeySpec and self.NumberOfBytes == __o.NumberOfBytes and self.GrantTokens == __o.GrantTokens
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateDataKeyWithoutPlaintextResponse:
    @classmethod
    def default(cls, ):
        return lambda: GenerateDataKeyWithoutPlaintextResponse_GenerateDataKeyWithoutPlaintextResponse(Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateDataKeyWithoutPlaintextResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyWithoutPlaintextResponse_GenerateDataKeyWithoutPlaintextResponse)

class GenerateDataKeyWithoutPlaintextResponse_GenerateDataKeyWithoutPlaintextResponse(GenerateDataKeyWithoutPlaintextResponse, NamedTuple('GenerateDataKeyWithoutPlaintextResponse', [('CiphertextBlob', Any), ('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateDataKeyWithoutPlaintextResponse.GenerateDataKeyWithoutPlaintextResponse({_dafny.string_of(self.CiphertextBlob)}, {_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateDataKeyWithoutPlaintextResponse_GenerateDataKeyWithoutPlaintextResponse) and self.CiphertextBlob == __o.CiphertextBlob and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateRandomRequest:
    @classmethod
    def default(cls, ):
        return lambda: GenerateRandomRequest_GenerateRandomRequest(Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateRandomRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateRandomRequest_GenerateRandomRequest)

class GenerateRandomRequest_GenerateRandomRequest(GenerateRandomRequest, NamedTuple('GenerateRandomRequest', [('NumberOfBytes', Any), ('CustomKeyStoreId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateRandomRequest.GenerateRandomRequest({_dafny.string_of(self.NumberOfBytes)}, {_dafny.string_of(self.CustomKeyStoreId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateRandomRequest_GenerateRandomRequest) and self.NumberOfBytes == __o.NumberOfBytes and self.CustomKeyStoreId == __o.CustomKeyStoreId
    def __hash__(self) -> int:
        return super().__hash__()


class GenerateRandomResponse:
    @classmethod
    def default(cls, ):
        return lambda: GenerateRandomResponse_GenerateRandomResponse(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GenerateRandomResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GenerateRandomResponse_GenerateRandomResponse)

class GenerateRandomResponse_GenerateRandomResponse(GenerateRandomResponse, NamedTuple('GenerateRandomResponse', [('Plaintext', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GenerateRandomResponse.GenerateRandomResponse({_dafny.string_of(self.Plaintext)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GenerateRandomResponse_GenerateRandomResponse) and self.Plaintext == __o.Plaintext
    def __hash__(self) -> int:
        return super().__hash__()


class GetKeyPolicyRequest:
    @classmethod
    def default(cls, ):
        return lambda: GetKeyPolicyRequest_GetKeyPolicyRequest(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetKeyPolicyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GetKeyPolicyRequest_GetKeyPolicyRequest)

class GetKeyPolicyRequest_GetKeyPolicyRequest(GetKeyPolicyRequest, NamedTuple('GetKeyPolicyRequest', [('KeyId', Any), ('PolicyName', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GetKeyPolicyRequest.GetKeyPolicyRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.PolicyName)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GetKeyPolicyRequest_GetKeyPolicyRequest) and self.KeyId == __o.KeyId and self.PolicyName == __o.PolicyName
    def __hash__(self) -> int:
        return super().__hash__()


class GetKeyPolicyResponse:
    @classmethod
    def default(cls, ):
        return lambda: GetKeyPolicyResponse_GetKeyPolicyResponse(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetKeyPolicyResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GetKeyPolicyResponse_GetKeyPolicyResponse)

class GetKeyPolicyResponse_GetKeyPolicyResponse(GetKeyPolicyResponse, NamedTuple('GetKeyPolicyResponse', [('Policy', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GetKeyPolicyResponse.GetKeyPolicyResponse({_dafny.string_of(self.Policy)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GetKeyPolicyResponse_GetKeyPolicyResponse) and self.Policy == __o.Policy
    def __hash__(self) -> int:
        return super().__hash__()


class GetKeyRotationStatusRequest:
    @classmethod
    def default(cls, ):
        return lambda: GetKeyRotationStatusRequest_GetKeyRotationStatusRequest(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetKeyRotationStatusRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GetKeyRotationStatusRequest_GetKeyRotationStatusRequest)

class GetKeyRotationStatusRequest_GetKeyRotationStatusRequest(GetKeyRotationStatusRequest, NamedTuple('GetKeyRotationStatusRequest', [('KeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GetKeyRotationStatusRequest.GetKeyRotationStatusRequest({_dafny.string_of(self.KeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GetKeyRotationStatusRequest_GetKeyRotationStatusRequest) and self.KeyId == __o.KeyId
    def __hash__(self) -> int:
        return super().__hash__()


class GetKeyRotationStatusResponse:
    @classmethod
    def default(cls, ):
        return lambda: GetKeyRotationStatusResponse_GetKeyRotationStatusResponse(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetKeyRotationStatusResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GetKeyRotationStatusResponse_GetKeyRotationStatusResponse)

class GetKeyRotationStatusResponse_GetKeyRotationStatusResponse(GetKeyRotationStatusResponse, NamedTuple('GetKeyRotationStatusResponse', [('KeyRotationEnabled', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GetKeyRotationStatusResponse.GetKeyRotationStatusResponse({_dafny.string_of(self.KeyRotationEnabled)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GetKeyRotationStatusResponse_GetKeyRotationStatusResponse) and self.KeyRotationEnabled == __o.KeyRotationEnabled
    def __hash__(self) -> int:
        return super().__hash__()


class GetParametersForImportRequest:
    @classmethod
    def default(cls, ):
        return lambda: GetParametersForImportRequest_GetParametersForImportRequest(_dafny.Seq({}), software_amazon_cryptography_services_kms_internaldafny_types.AlgorithmSpec.default()(), software_amazon_cryptography_services_kms_internaldafny_types.WrappingKeySpec.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetParametersForImportRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GetParametersForImportRequest_GetParametersForImportRequest)

class GetParametersForImportRequest_GetParametersForImportRequest(GetParametersForImportRequest, NamedTuple('GetParametersForImportRequest', [('KeyId', Any), ('WrappingAlgorithm', Any), ('WrappingKeySpec', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GetParametersForImportRequest.GetParametersForImportRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.WrappingAlgorithm)}, {_dafny.string_of(self.WrappingKeySpec)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GetParametersForImportRequest_GetParametersForImportRequest) and self.KeyId == __o.KeyId and self.WrappingAlgorithm == __o.WrappingAlgorithm and self.WrappingKeySpec == __o.WrappingKeySpec
    def __hash__(self) -> int:
        return super().__hash__()


class GetParametersForImportResponse:
    @classmethod
    def default(cls, ):
        return lambda: GetParametersForImportResponse_GetParametersForImportResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetParametersForImportResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GetParametersForImportResponse_GetParametersForImportResponse)

class GetParametersForImportResponse_GetParametersForImportResponse(GetParametersForImportResponse, NamedTuple('GetParametersForImportResponse', [('KeyId', Any), ('ImportToken', Any), ('PublicKey', Any), ('ParametersValidTo', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GetParametersForImportResponse.GetParametersForImportResponse({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.ImportToken)}, {_dafny.string_of(self.PublicKey)}, {_dafny.string_of(self.ParametersValidTo)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GetParametersForImportResponse_GetParametersForImportResponse) and self.KeyId == __o.KeyId and self.ImportToken == __o.ImportToken and self.PublicKey == __o.PublicKey and self.ParametersValidTo == __o.ParametersValidTo
    def __hash__(self) -> int:
        return super().__hash__()


class GetPublicKeyRequest:
    @classmethod
    def default(cls, ):
        return lambda: GetPublicKeyRequest_GetPublicKeyRequest(_dafny.Seq({}), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetPublicKeyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GetPublicKeyRequest_GetPublicKeyRequest)

class GetPublicKeyRequest_GetPublicKeyRequest(GetPublicKeyRequest, NamedTuple('GetPublicKeyRequest', [('KeyId', Any), ('GrantTokens', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GetPublicKeyRequest.GetPublicKeyRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.GrantTokens)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GetPublicKeyRequest_GetPublicKeyRequest) and self.KeyId == __o.KeyId and self.GrantTokens == __o.GrantTokens
    def __hash__(self) -> int:
        return super().__hash__()


class GetPublicKeyResponse:
    @classmethod
    def default(cls, ):
        return lambda: GetPublicKeyResponse_GetPublicKeyResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetPublicKeyResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GetPublicKeyResponse_GetPublicKeyResponse)

class GetPublicKeyResponse_GetPublicKeyResponse(GetPublicKeyResponse, NamedTuple('GetPublicKeyResponse', [('KeyId', Any), ('PublicKey', Any), ('CustomerMasterKeySpec', Any), ('KeySpec', Any), ('KeyUsage', Any), ('EncryptionAlgorithms', Any), ('SigningAlgorithms', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GetPublicKeyResponse.GetPublicKeyResponse({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.PublicKey)}, {_dafny.string_of(self.CustomerMasterKeySpec)}, {_dafny.string_of(self.KeySpec)}, {_dafny.string_of(self.KeyUsage)}, {_dafny.string_of(self.EncryptionAlgorithms)}, {_dafny.string_of(self.SigningAlgorithms)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GetPublicKeyResponse_GetPublicKeyResponse) and self.KeyId == __o.KeyId and self.PublicKey == __o.PublicKey and self.CustomerMasterKeySpec == __o.CustomerMasterKeySpec and self.KeySpec == __o.KeySpec and self.KeyUsage == __o.KeyUsage and self.EncryptionAlgorithms == __o.EncryptionAlgorithms and self.SigningAlgorithms == __o.SigningAlgorithms
    def __hash__(self) -> int:
        return super().__hash__()


class GrantConstraints:
    @classmethod
    def default(cls, ):
        return lambda: GrantConstraints_GrantConstraints(Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GrantConstraints(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantConstraints_GrantConstraints)

class GrantConstraints_GrantConstraints(GrantConstraints, NamedTuple('GrantConstraints', [('EncryptionContextSubset', Any), ('EncryptionContextEquals', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantConstraints.GrantConstraints({_dafny.string_of(self.EncryptionContextSubset)}, {_dafny.string_of(self.EncryptionContextEquals)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantConstraints_GrantConstraints) and self.EncryptionContextSubset == __o.EncryptionContextSubset and self.EncryptionContextEquals == __o.EncryptionContextEquals
    def __hash__(self) -> int:
        return super().__hash__()


class GrantIdType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class GrantListEntry:
    @classmethod
    def default(cls, ):
        return lambda: GrantListEntry_GrantListEntry(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GrantListEntry(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantListEntry_GrantListEntry)

class GrantListEntry_GrantListEntry(GrantListEntry, NamedTuple('GrantListEntry', [('KeyId', Any), ('GrantId', Any), ('Name', Any), ('CreationDate', Any), ('GranteePrincipal', Any), ('RetiringPrincipal', Any), ('IssuingAccount', Any), ('Operations', Any), ('Constraints', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantListEntry.GrantListEntry({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.GrantId)}, {_dafny.string_of(self.Name)}, {_dafny.string_of(self.CreationDate)}, {_dafny.string_of(self.GranteePrincipal)}, {_dafny.string_of(self.RetiringPrincipal)}, {_dafny.string_of(self.IssuingAccount)}, {_dafny.string_of(self.Operations)}, {_dafny.string_of(self.Constraints)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantListEntry_GrantListEntry) and self.KeyId == __o.KeyId and self.GrantId == __o.GrantId and self.Name == __o.Name and self.CreationDate == __o.CreationDate and self.GranteePrincipal == __o.GranteePrincipal and self.RetiringPrincipal == __o.RetiringPrincipal and self.IssuingAccount == __o.IssuingAccount and self.Operations == __o.Operations and self.Constraints == __o.Constraints
    def __hash__(self) -> int:
        return super().__hash__()


class GrantNameType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class GrantOperation:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [GrantOperation_Decrypt(), GrantOperation_Encrypt(), GrantOperation_GenerateDataKey(), GrantOperation_GenerateDataKeyWithoutPlaintext(), GrantOperation_ReEncryptFrom(), GrantOperation_ReEncryptTo(), GrantOperation_Sign(), GrantOperation_Verify(), GrantOperation_GetPublicKey(), GrantOperation_CreateGrant(), GrantOperation_RetireGrant(), GrantOperation_DescribeKey(), GrantOperation_GenerateDataKeyPair(), GrantOperation_GenerateDataKeyPairWithoutPlaintext()]
    @classmethod
    def default(cls, ):
        return lambda: GrantOperation_Decrypt()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Decrypt(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_Decrypt)
    @property
    def is_Encrypt(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_Encrypt)
    @property
    def is_GenerateDataKey(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GenerateDataKey)
    @property
    def is_GenerateDataKeyWithoutPlaintext(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GenerateDataKeyWithoutPlaintext)
    @property
    def is_ReEncryptFrom(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_ReEncryptFrom)
    @property
    def is_ReEncryptTo(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_ReEncryptTo)
    @property
    def is_Sign(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_Sign)
    @property
    def is_Verify(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_Verify)
    @property
    def is_GetPublicKey(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GetPublicKey)
    @property
    def is_CreateGrant(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_CreateGrant)
    @property
    def is_RetireGrant(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_RetireGrant)
    @property
    def is_DescribeKey(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_DescribeKey)
    @property
    def is_GenerateDataKeyPair(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GenerateDataKeyPair)
    @property
    def is_GenerateDataKeyPairWithoutPlaintext(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GenerateDataKeyPairWithoutPlaintext)

class GrantOperation_Decrypt(GrantOperation, NamedTuple('Decrypt', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.Decrypt'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_Decrypt)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_Encrypt(GrantOperation, NamedTuple('Encrypt', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.Encrypt'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_Encrypt)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_GenerateDataKey(GrantOperation, NamedTuple('GenerateDataKey', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.GenerateDataKey'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GenerateDataKey)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_GenerateDataKeyWithoutPlaintext(GrantOperation, NamedTuple('GenerateDataKeyWithoutPlaintext', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.GenerateDataKeyWithoutPlaintext'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GenerateDataKeyWithoutPlaintext)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_ReEncryptFrom(GrantOperation, NamedTuple('ReEncryptFrom', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.ReEncryptFrom'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_ReEncryptFrom)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_ReEncryptTo(GrantOperation, NamedTuple('ReEncryptTo', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.ReEncryptTo'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_ReEncryptTo)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_Sign(GrantOperation, NamedTuple('Sign', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.Sign'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_Sign)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_Verify(GrantOperation, NamedTuple('Verify', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.Verify'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_Verify)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_GetPublicKey(GrantOperation, NamedTuple('GetPublicKey', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.GetPublicKey'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GetPublicKey)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_CreateGrant(GrantOperation, NamedTuple('CreateGrant', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.CreateGrant'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_CreateGrant)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_RetireGrant(GrantOperation, NamedTuple('RetireGrant', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.RetireGrant'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_RetireGrant)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_DescribeKey(GrantOperation, NamedTuple('DescribeKey', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.DescribeKey'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_DescribeKey)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_GenerateDataKeyPair(GrantOperation, NamedTuple('GenerateDataKeyPair', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.GenerateDataKeyPair'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GenerateDataKeyPair)
    def __hash__(self) -> int:
        return super().__hash__()

class GrantOperation_GenerateDataKeyPairWithoutPlaintext(GrantOperation, NamedTuple('GenerateDataKeyPairWithoutPlaintext', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.GrantOperation.GenerateDataKeyPairWithoutPlaintext'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.GrantOperation_GenerateDataKeyPairWithoutPlaintext)
    def __hash__(self) -> int:
        return super().__hash__()


class GrantTokenList:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class GrantTokenType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class ImportKeyMaterialRequest:
    @classmethod
    def default(cls, ):
        return lambda: ImportKeyMaterialRequest_ImportKeyMaterialRequest(_dafny.Seq({}), _dafny.Seq({}), _dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ImportKeyMaterialRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ImportKeyMaterialRequest_ImportKeyMaterialRequest)

class ImportKeyMaterialRequest_ImportKeyMaterialRequest(ImportKeyMaterialRequest, NamedTuple('ImportKeyMaterialRequest', [('KeyId', Any), ('ImportToken', Any), ('EncryptedKeyMaterial', Any), ('ValidTo', Any), ('ExpirationModel', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ImportKeyMaterialRequest.ImportKeyMaterialRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.ImportToken)}, {_dafny.string_of(self.EncryptedKeyMaterial)}, {_dafny.string_of(self.ValidTo)}, {_dafny.string_of(self.ExpirationModel)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ImportKeyMaterialRequest_ImportKeyMaterialRequest) and self.KeyId == __o.KeyId and self.ImportToken == __o.ImportToken and self.EncryptedKeyMaterial == __o.EncryptedKeyMaterial and self.ValidTo == __o.ValidTo and self.ExpirationModel == __o.ExpirationModel
    def __hash__(self) -> int:
        return super().__hash__()


class ImportKeyMaterialResponse:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [ImportKeyMaterialResponse_ImportKeyMaterialResponse()]
    @classmethod
    def default(cls, ):
        return lambda: ImportKeyMaterialResponse_ImportKeyMaterialResponse()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ImportKeyMaterialResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ImportKeyMaterialResponse_ImportKeyMaterialResponse)

class ImportKeyMaterialResponse_ImportKeyMaterialResponse(ImportKeyMaterialResponse, NamedTuple('ImportKeyMaterialResponse', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ImportKeyMaterialResponse.ImportKeyMaterialResponse'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ImportKeyMaterialResponse_ImportKeyMaterialResponse)
    def __hash__(self) -> int:
        return super().__hash__()


class KeyIdType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class KeyListEntry:
    @classmethod
    def default(cls, ):
        return lambda: KeyListEntry_KeyListEntry(Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_KeyListEntry(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyListEntry_KeyListEntry)

class KeyListEntry_KeyListEntry(KeyListEntry, NamedTuple('KeyListEntry', [('KeyId', Any), ('KeyArn', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyListEntry.KeyListEntry({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.KeyArn)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyListEntry_KeyListEntry) and self.KeyId == __o.KeyId and self.KeyArn == __o.KeyArn
    def __hash__(self) -> int:
        return super().__hash__()


class KeyManagerType:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [KeyManagerType_AWS(), KeyManagerType_CUSTOMER()]
    @classmethod
    def default(cls, ):
        return lambda: KeyManagerType_AWS()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_AWS(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyManagerType_AWS)
    @property
    def is_CUSTOMER(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyManagerType_CUSTOMER)

class KeyManagerType_AWS(KeyManagerType, NamedTuple('AWS', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyManagerType.AWS'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyManagerType_AWS)
    def __hash__(self) -> int:
        return super().__hash__()

class KeyManagerType_CUSTOMER(KeyManagerType, NamedTuple('CUSTOMER', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyManagerType.CUSTOMER'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyManagerType_CUSTOMER)
    def __hash__(self) -> int:
        return super().__hash__()


class KeyMetadata:
    @classmethod
    def default(cls, ):
        return lambda: KeyMetadata_KeyMetadata(Wrappers.Option.default()(), _dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_KeyMetadata(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyMetadata_KeyMetadata)

class KeyMetadata_KeyMetadata(KeyMetadata, NamedTuple('KeyMetadata', [('AWSAccountId', Any), ('KeyId', Any), ('Arn', Any), ('CreationDate', Any), ('Enabled', Any), ('Description', Any), ('KeyUsage', Any), ('KeyState', Any), ('DeletionDate', Any), ('ValidTo', Any), ('Origin', Any), ('CustomKeyStoreId', Any), ('CloudHsmClusterId', Any), ('ExpirationModel', Any), ('KeyManager', Any), ('CustomerMasterKeySpec', Any), ('KeySpec', Any), ('EncryptionAlgorithms', Any), ('SigningAlgorithms', Any), ('MultiRegion', Any), ('MultiRegionConfiguration', Any), ('PendingDeletionWindowInDays', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyMetadata.KeyMetadata({_dafny.string_of(self.AWSAccountId)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Arn)}, {_dafny.string_of(self.CreationDate)}, {_dafny.string_of(self.Enabled)}, {_dafny.string_of(self.Description)}, {_dafny.string_of(self.KeyUsage)}, {_dafny.string_of(self.KeyState)}, {_dafny.string_of(self.DeletionDate)}, {_dafny.string_of(self.ValidTo)}, {_dafny.string_of(self.Origin)}, {_dafny.string_of(self.CustomKeyStoreId)}, {_dafny.string_of(self.CloudHsmClusterId)}, {_dafny.string_of(self.ExpirationModel)}, {_dafny.string_of(self.KeyManager)}, {_dafny.string_of(self.CustomerMasterKeySpec)}, {_dafny.string_of(self.KeySpec)}, {_dafny.string_of(self.EncryptionAlgorithms)}, {_dafny.string_of(self.SigningAlgorithms)}, {_dafny.string_of(self.MultiRegion)}, {_dafny.string_of(self.MultiRegionConfiguration)}, {_dafny.string_of(self.PendingDeletionWindowInDays)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyMetadata_KeyMetadata) and self.AWSAccountId == __o.AWSAccountId and self.KeyId == __o.KeyId and self.Arn == __o.Arn and self.CreationDate == __o.CreationDate and self.Enabled == __o.Enabled and self.Description == __o.Description and self.KeyUsage == __o.KeyUsage and self.KeyState == __o.KeyState and self.DeletionDate == __o.DeletionDate and self.ValidTo == __o.ValidTo and self.Origin == __o.Origin and self.CustomKeyStoreId == __o.CustomKeyStoreId and self.CloudHsmClusterId == __o.CloudHsmClusterId and self.ExpirationModel == __o.ExpirationModel and self.KeyManager == __o.KeyManager and self.CustomerMasterKeySpec == __o.CustomerMasterKeySpec and self.KeySpec == __o.KeySpec and self.EncryptionAlgorithms == __o.EncryptionAlgorithms and self.SigningAlgorithms == __o.SigningAlgorithms and self.MultiRegion == __o.MultiRegion and self.MultiRegionConfiguration == __o.MultiRegionConfiguration and self.PendingDeletionWindowInDays == __o.PendingDeletionWindowInDays
    def __hash__(self) -> int:
        return super().__hash__()


class KeySpec:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [KeySpec_RSA__2048(), KeySpec_RSA__3072(), KeySpec_RSA__4096(), KeySpec_ECC__NIST__P256(), KeySpec_ECC__NIST__P384(), KeySpec_ECC__NIST__P521(), KeySpec_ECC__SECG__P256K1(), KeySpec_SYMMETRIC__DEFAULT()]
    @classmethod
    def default(cls, ):
        return lambda: KeySpec_RSA__2048()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_RSA__2048(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_RSA__2048)
    @property
    def is_RSA__3072(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_RSA__3072)
    @property
    def is_RSA__4096(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_RSA__4096)
    @property
    def is_ECC__NIST__P256(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_ECC__NIST__P256)
    @property
    def is_ECC__NIST__P384(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_ECC__NIST__P384)
    @property
    def is_ECC__NIST__P521(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_ECC__NIST__P521)
    @property
    def is_ECC__SECG__P256K1(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_ECC__SECG__P256K1)
    @property
    def is_SYMMETRIC__DEFAULT(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_SYMMETRIC__DEFAULT)

class KeySpec_RSA__2048(KeySpec, NamedTuple('RSA__2048', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeySpec.RSA_2048'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_RSA__2048)
    def __hash__(self) -> int:
        return super().__hash__()

class KeySpec_RSA__3072(KeySpec, NamedTuple('RSA__3072', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeySpec.RSA_3072'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_RSA__3072)
    def __hash__(self) -> int:
        return super().__hash__()

class KeySpec_RSA__4096(KeySpec, NamedTuple('RSA__4096', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeySpec.RSA_4096'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_RSA__4096)
    def __hash__(self) -> int:
        return super().__hash__()

class KeySpec_ECC__NIST__P256(KeySpec, NamedTuple('ECC__NIST__P256', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeySpec.ECC_NIST_P256'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_ECC__NIST__P256)
    def __hash__(self) -> int:
        return super().__hash__()

class KeySpec_ECC__NIST__P384(KeySpec, NamedTuple('ECC__NIST__P384', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeySpec.ECC_NIST_P384'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_ECC__NIST__P384)
    def __hash__(self) -> int:
        return super().__hash__()

class KeySpec_ECC__NIST__P521(KeySpec, NamedTuple('ECC__NIST__P521', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeySpec.ECC_NIST_P521'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_ECC__NIST__P521)
    def __hash__(self) -> int:
        return super().__hash__()

class KeySpec_ECC__SECG__P256K1(KeySpec, NamedTuple('ECC__SECG__P256K1', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeySpec.ECC_SECG_P256K1'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_ECC__SECG__P256K1)
    def __hash__(self) -> int:
        return super().__hash__()

class KeySpec_SYMMETRIC__DEFAULT(KeySpec, NamedTuple('SYMMETRIC__DEFAULT', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeySpec.SYMMETRIC_DEFAULT'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeySpec_SYMMETRIC__DEFAULT)
    def __hash__(self) -> int:
        return super().__hash__()


class KeyState:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [KeyState_Creating(), KeyState_Enabled(), KeyState_Disabled(), KeyState_PendingDeletion(), KeyState_PendingImport(), KeyState_PendingReplicaDeletion(), KeyState_Unavailable(), KeyState_Updating()]
    @classmethod
    def default(cls, ):
        return lambda: KeyState_Creating()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Creating(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Creating)
    @property
    def is_Enabled(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Enabled)
    @property
    def is_Disabled(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Disabled)
    @property
    def is_PendingDeletion(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_PendingDeletion)
    @property
    def is_PendingImport(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_PendingImport)
    @property
    def is_PendingReplicaDeletion(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_PendingReplicaDeletion)
    @property
    def is_Unavailable(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Unavailable)
    @property
    def is_Updating(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Updating)

class KeyState_Creating(KeyState, NamedTuple('Creating', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyState.Creating'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Creating)
    def __hash__(self) -> int:
        return super().__hash__()

class KeyState_Enabled(KeyState, NamedTuple('Enabled', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyState.Enabled'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Enabled)
    def __hash__(self) -> int:
        return super().__hash__()

class KeyState_Disabled(KeyState, NamedTuple('Disabled', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyState.Disabled'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Disabled)
    def __hash__(self) -> int:
        return super().__hash__()

class KeyState_PendingDeletion(KeyState, NamedTuple('PendingDeletion', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyState.PendingDeletion'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_PendingDeletion)
    def __hash__(self) -> int:
        return super().__hash__()

class KeyState_PendingImport(KeyState, NamedTuple('PendingImport', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyState.PendingImport'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_PendingImport)
    def __hash__(self) -> int:
        return super().__hash__()

class KeyState_PendingReplicaDeletion(KeyState, NamedTuple('PendingReplicaDeletion', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyState.PendingReplicaDeletion'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_PendingReplicaDeletion)
    def __hash__(self) -> int:
        return super().__hash__()

class KeyState_Unavailable(KeyState, NamedTuple('Unavailable', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyState.Unavailable'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Unavailable)
    def __hash__(self) -> int:
        return super().__hash__()

class KeyState_Updating(KeyState, NamedTuple('Updating', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyState.Updating'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyState_Updating)
    def __hash__(self) -> int:
        return super().__hash__()


class KeyStorePasswordType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class KeyUsageType:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [KeyUsageType_SIGN__VERIFY(), KeyUsageType_ENCRYPT__DECRYPT()]
    @classmethod
    def default(cls, ):
        return lambda: KeyUsageType_SIGN__VERIFY()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SIGN__VERIFY(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyUsageType_SIGN__VERIFY)
    @property
    def is_ENCRYPT__DECRYPT(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.KeyUsageType_ENCRYPT__DECRYPT)

class KeyUsageType_SIGN__VERIFY(KeyUsageType, NamedTuple('SIGN__VERIFY', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyUsageType.SIGN_VERIFY'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyUsageType_SIGN__VERIFY)
    def __hash__(self) -> int:
        return super().__hash__()

class KeyUsageType_ENCRYPT__DECRYPT(KeyUsageType, NamedTuple('ENCRYPT__DECRYPT', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.KeyUsageType.ENCRYPT_DECRYPT'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.KeyUsageType_ENCRYPT__DECRYPT)
    def __hash__(self) -> int:
        return super().__hash__()


class LimitType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class ListAliasesRequest:
    @classmethod
    def default(cls, ):
        return lambda: ListAliasesRequest_ListAliasesRequest(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListAliasesRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListAliasesRequest_ListAliasesRequest)

class ListAliasesRequest_ListAliasesRequest(ListAliasesRequest, NamedTuple('ListAliasesRequest', [('KeyId', Any), ('Limit', Any), ('Marker', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListAliasesRequest.ListAliasesRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Limit)}, {_dafny.string_of(self.Marker)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListAliasesRequest_ListAliasesRequest) and self.KeyId == __o.KeyId and self.Limit == __o.Limit and self.Marker == __o.Marker
    def __hash__(self) -> int:
        return super().__hash__()


class ListAliasesResponse:
    @classmethod
    def default(cls, ):
        return lambda: ListAliasesResponse_ListAliasesResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListAliasesResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListAliasesResponse_ListAliasesResponse)

class ListAliasesResponse_ListAliasesResponse(ListAliasesResponse, NamedTuple('ListAliasesResponse', [('Aliases', Any), ('NextMarker', Any), ('Truncated', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListAliasesResponse.ListAliasesResponse({_dafny.string_of(self.Aliases)}, {_dafny.string_of(self.NextMarker)}, {_dafny.string_of(self.Truncated)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListAliasesResponse_ListAliasesResponse) and self.Aliases == __o.Aliases and self.NextMarker == __o.NextMarker and self.Truncated == __o.Truncated
    def __hash__(self) -> int:
        return super().__hash__()


class ListGrantsRequest:
    @classmethod
    def default(cls, ):
        return lambda: ListGrantsRequest_ListGrantsRequest(Wrappers.Option.default()(), Wrappers.Option.default()(), _dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListGrantsRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListGrantsRequest_ListGrantsRequest)

class ListGrantsRequest_ListGrantsRequest(ListGrantsRequest, NamedTuple('ListGrantsRequest', [('Limit', Any), ('Marker', Any), ('KeyId', Any), ('GrantId', Any), ('GranteePrincipal', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListGrantsRequest.ListGrantsRequest({_dafny.string_of(self.Limit)}, {_dafny.string_of(self.Marker)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.GrantId)}, {_dafny.string_of(self.GranteePrincipal)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListGrantsRequest_ListGrantsRequest) and self.Limit == __o.Limit and self.Marker == __o.Marker and self.KeyId == __o.KeyId and self.GrantId == __o.GrantId and self.GranteePrincipal == __o.GranteePrincipal
    def __hash__(self) -> int:
        return super().__hash__()


class ListGrantsResponse:
    @classmethod
    def default(cls, ):
        return lambda: ListGrantsResponse_ListGrantsResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListGrantsResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListGrantsResponse_ListGrantsResponse)

class ListGrantsResponse_ListGrantsResponse(ListGrantsResponse, NamedTuple('ListGrantsResponse', [('Grants', Any), ('NextMarker', Any), ('Truncated', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListGrantsResponse.ListGrantsResponse({_dafny.string_of(self.Grants)}, {_dafny.string_of(self.NextMarker)}, {_dafny.string_of(self.Truncated)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListGrantsResponse_ListGrantsResponse) and self.Grants == __o.Grants and self.NextMarker == __o.NextMarker and self.Truncated == __o.Truncated
    def __hash__(self) -> int:
        return super().__hash__()


class ListKeyPoliciesRequest:
    @classmethod
    def default(cls, ):
        return lambda: ListKeyPoliciesRequest_ListKeyPoliciesRequest(_dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListKeyPoliciesRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListKeyPoliciesRequest_ListKeyPoliciesRequest)

class ListKeyPoliciesRequest_ListKeyPoliciesRequest(ListKeyPoliciesRequest, NamedTuple('ListKeyPoliciesRequest', [('KeyId', Any), ('Limit', Any), ('Marker', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListKeyPoliciesRequest.ListKeyPoliciesRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Limit)}, {_dafny.string_of(self.Marker)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListKeyPoliciesRequest_ListKeyPoliciesRequest) and self.KeyId == __o.KeyId and self.Limit == __o.Limit and self.Marker == __o.Marker
    def __hash__(self) -> int:
        return super().__hash__()


class ListKeyPoliciesResponse:
    @classmethod
    def default(cls, ):
        return lambda: ListKeyPoliciesResponse_ListKeyPoliciesResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListKeyPoliciesResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListKeyPoliciesResponse_ListKeyPoliciesResponse)

class ListKeyPoliciesResponse_ListKeyPoliciesResponse(ListKeyPoliciesResponse, NamedTuple('ListKeyPoliciesResponse', [('PolicyNames', Any), ('NextMarker', Any), ('Truncated', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListKeyPoliciesResponse.ListKeyPoliciesResponse({_dafny.string_of(self.PolicyNames)}, {_dafny.string_of(self.NextMarker)}, {_dafny.string_of(self.Truncated)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListKeyPoliciesResponse_ListKeyPoliciesResponse) and self.PolicyNames == __o.PolicyNames and self.NextMarker == __o.NextMarker and self.Truncated == __o.Truncated
    def __hash__(self) -> int:
        return super().__hash__()


class ListKeysRequest:
    @classmethod
    def default(cls, ):
        return lambda: ListKeysRequest_ListKeysRequest(Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListKeysRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListKeysRequest_ListKeysRequest)

class ListKeysRequest_ListKeysRequest(ListKeysRequest, NamedTuple('ListKeysRequest', [('Limit', Any), ('Marker', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListKeysRequest.ListKeysRequest({_dafny.string_of(self.Limit)}, {_dafny.string_of(self.Marker)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListKeysRequest_ListKeysRequest) and self.Limit == __o.Limit and self.Marker == __o.Marker
    def __hash__(self) -> int:
        return super().__hash__()


class ListResourceTagsRequest:
    @classmethod
    def default(cls, ):
        return lambda: ListResourceTagsRequest_ListResourceTagsRequest(_dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListResourceTagsRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListResourceTagsRequest_ListResourceTagsRequest)

class ListResourceTagsRequest_ListResourceTagsRequest(ListResourceTagsRequest, NamedTuple('ListResourceTagsRequest', [('KeyId', Any), ('Limit', Any), ('Marker', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListResourceTagsRequest.ListResourceTagsRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Limit)}, {_dafny.string_of(self.Marker)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListResourceTagsRequest_ListResourceTagsRequest) and self.KeyId == __o.KeyId and self.Limit == __o.Limit and self.Marker == __o.Marker
    def __hash__(self) -> int:
        return super().__hash__()


class ListResourceTagsResponse:
    @classmethod
    def default(cls, ):
        return lambda: ListResourceTagsResponse_ListResourceTagsResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListResourceTagsResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListResourceTagsResponse_ListResourceTagsResponse)

class ListResourceTagsResponse_ListResourceTagsResponse(ListResourceTagsResponse, NamedTuple('ListResourceTagsResponse', [('Tags', Any), ('NextMarker', Any), ('Truncated', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListResourceTagsResponse.ListResourceTagsResponse({_dafny.string_of(self.Tags)}, {_dafny.string_of(self.NextMarker)}, {_dafny.string_of(self.Truncated)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListResourceTagsResponse_ListResourceTagsResponse) and self.Tags == __o.Tags and self.NextMarker == __o.NextMarker and self.Truncated == __o.Truncated
    def __hash__(self) -> int:
        return super().__hash__()


class ListRetirableGrantsRequest:
    @classmethod
    def default(cls, ):
        return lambda: ListRetirableGrantsRequest_ListRetirableGrantsRequest(Wrappers.Option.default()(), Wrappers.Option.default()(), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ListRetirableGrantsRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ListRetirableGrantsRequest_ListRetirableGrantsRequest)

class ListRetirableGrantsRequest_ListRetirableGrantsRequest(ListRetirableGrantsRequest, NamedTuple('ListRetirableGrantsRequest', [('Limit', Any), ('Marker', Any), ('RetiringPrincipal', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ListRetirableGrantsRequest.ListRetirableGrantsRequest({_dafny.string_of(self.Limit)}, {_dafny.string_of(self.Marker)}, {_dafny.string_of(self.RetiringPrincipal)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ListRetirableGrantsRequest_ListRetirableGrantsRequest) and self.Limit == __o.Limit and self.Marker == __o.Marker and self.RetiringPrincipal == __o.RetiringPrincipal
    def __hash__(self) -> int:
        return super().__hash__()


class MarkerType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class MessageType:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [MessageType_RAW(), MessageType_DIGEST()]
    @classmethod
    def default(cls, ):
        return lambda: MessageType_RAW()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_RAW(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.MessageType_RAW)
    @property
    def is_DIGEST(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.MessageType_DIGEST)

class MessageType_RAW(MessageType, NamedTuple('RAW', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.MessageType.RAW'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.MessageType_RAW)
    def __hash__(self) -> int:
        return super().__hash__()

class MessageType_DIGEST(MessageType, NamedTuple('DIGEST', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.MessageType.DIGEST'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.MessageType_DIGEST)
    def __hash__(self) -> int:
        return super().__hash__()


class MultiRegionConfiguration:
    @classmethod
    def default(cls, ):
        return lambda: MultiRegionConfiguration_MultiRegionConfiguration(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_MultiRegionConfiguration(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.MultiRegionConfiguration_MultiRegionConfiguration)

class MultiRegionConfiguration_MultiRegionConfiguration(MultiRegionConfiguration, NamedTuple('MultiRegionConfiguration', [('MultiRegionKeyType', Any), ('PrimaryKey', Any), ('ReplicaKeys', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.MultiRegionConfiguration.MultiRegionConfiguration({_dafny.string_of(self.MultiRegionKeyType)}, {_dafny.string_of(self.PrimaryKey)}, {_dafny.string_of(self.ReplicaKeys)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.MultiRegionConfiguration_MultiRegionConfiguration) and self.MultiRegionKeyType == __o.MultiRegionKeyType and self.PrimaryKey == __o.PrimaryKey and self.ReplicaKeys == __o.ReplicaKeys
    def __hash__(self) -> int:
        return super().__hash__()


class MultiRegionKey:
    @classmethod
    def default(cls, ):
        return lambda: MultiRegionKey_MultiRegionKey(Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_MultiRegionKey(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.MultiRegionKey_MultiRegionKey)

class MultiRegionKey_MultiRegionKey(MultiRegionKey, NamedTuple('MultiRegionKey', [('Arn', Any), ('Region', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.MultiRegionKey.MultiRegionKey({_dafny.string_of(self.Arn)}, {_dafny.string_of(self.Region)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.MultiRegionKey_MultiRegionKey) and self.Arn == __o.Arn and self.Region == __o.Region
    def __hash__(self) -> int:
        return super().__hash__()


class MultiRegionKeyType:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [MultiRegionKeyType_PRIMARY(), MultiRegionKeyType_REPLICA()]
    @classmethod
    def default(cls, ):
        return lambda: MultiRegionKeyType_PRIMARY()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_PRIMARY(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.MultiRegionKeyType_PRIMARY)
    @property
    def is_REPLICA(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.MultiRegionKeyType_REPLICA)

class MultiRegionKeyType_PRIMARY(MultiRegionKeyType, NamedTuple('PRIMARY', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.MultiRegionKeyType.PRIMARY'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.MultiRegionKeyType_PRIMARY)
    def __hash__(self) -> int:
        return super().__hash__()

class MultiRegionKeyType_REPLICA(MultiRegionKeyType, NamedTuple('REPLICA', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.MultiRegionKeyType.REPLICA'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.MultiRegionKeyType_REPLICA)
    def __hash__(self) -> int:
        return super().__hash__()


class NumberOfBytesType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class OriginType:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [OriginType_AWS__KMS(), OriginType_EXTERNAL(), OriginType_AWS__CLOUDHSM()]
    @classmethod
    def default(cls, ):
        return lambda: OriginType_AWS__KMS()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_AWS__KMS(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.OriginType_AWS__KMS)
    @property
    def is_EXTERNAL(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.OriginType_EXTERNAL)
    @property
    def is_AWS__CLOUDHSM(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.OriginType_AWS__CLOUDHSM)

class OriginType_AWS__KMS(OriginType, NamedTuple('AWS__KMS', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.OriginType.AWS_KMS'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.OriginType_AWS__KMS)
    def __hash__(self) -> int:
        return super().__hash__()

class OriginType_EXTERNAL(OriginType, NamedTuple('EXTERNAL', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.OriginType.EXTERNAL'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.OriginType_EXTERNAL)
    def __hash__(self) -> int:
        return super().__hash__()

class OriginType_AWS__CLOUDHSM(OriginType, NamedTuple('AWS__CLOUDHSM', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.OriginType.AWS_CLOUDHSM'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.OriginType_AWS__CLOUDHSM)
    def __hash__(self) -> int:
        return super().__hash__()


class PendingWindowInDaysType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)

class PlaintextType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class PolicyNameType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class PolicyType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class PrincipalIdType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class PublicKeyType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class PutKeyPolicyRequest:
    @classmethod
    def default(cls, ):
        return lambda: PutKeyPolicyRequest_PutKeyPolicyRequest(_dafny.Seq({}), _dafny.Seq({}), _dafny.Seq({}), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_PutKeyPolicyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.PutKeyPolicyRequest_PutKeyPolicyRequest)

class PutKeyPolicyRequest_PutKeyPolicyRequest(PutKeyPolicyRequest, NamedTuple('PutKeyPolicyRequest', [('KeyId', Any), ('PolicyName', Any), ('Policy', Any), ('BypassPolicyLockoutSafetyCheck', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.PutKeyPolicyRequest.PutKeyPolicyRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.PolicyName)}, {_dafny.string_of(self.Policy)}, {_dafny.string_of(self.BypassPolicyLockoutSafetyCheck)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.PutKeyPolicyRequest_PutKeyPolicyRequest) and self.KeyId == __o.KeyId and self.PolicyName == __o.PolicyName and self.Policy == __o.Policy and self.BypassPolicyLockoutSafetyCheck == __o.BypassPolicyLockoutSafetyCheck
    def __hash__(self) -> int:
        return super().__hash__()


class ReEncryptRequest:
    @classmethod
    def default(cls, ):
        return lambda: ReEncryptRequest_ReEncryptRequest(_dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), _dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ReEncryptRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ReEncryptRequest_ReEncryptRequest)

class ReEncryptRequest_ReEncryptRequest(ReEncryptRequest, NamedTuple('ReEncryptRequest', [('CiphertextBlob', Any), ('SourceEncryptionContext', Any), ('SourceKeyId', Any), ('DestinationKeyId', Any), ('DestinationEncryptionContext', Any), ('SourceEncryptionAlgorithm', Any), ('DestinationEncryptionAlgorithm', Any), ('GrantTokens', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ReEncryptRequest.ReEncryptRequest({_dafny.string_of(self.CiphertextBlob)}, {_dafny.string_of(self.SourceEncryptionContext)}, {_dafny.string_of(self.SourceKeyId)}, {_dafny.string_of(self.DestinationKeyId)}, {_dafny.string_of(self.DestinationEncryptionContext)}, {_dafny.string_of(self.SourceEncryptionAlgorithm)}, {_dafny.string_of(self.DestinationEncryptionAlgorithm)}, {_dafny.string_of(self.GrantTokens)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ReEncryptRequest_ReEncryptRequest) and self.CiphertextBlob == __o.CiphertextBlob and self.SourceEncryptionContext == __o.SourceEncryptionContext and self.SourceKeyId == __o.SourceKeyId and self.DestinationKeyId == __o.DestinationKeyId and self.DestinationEncryptionContext == __o.DestinationEncryptionContext and self.SourceEncryptionAlgorithm == __o.SourceEncryptionAlgorithm and self.DestinationEncryptionAlgorithm == __o.DestinationEncryptionAlgorithm and self.GrantTokens == __o.GrantTokens
    def __hash__(self) -> int:
        return super().__hash__()


class ReEncryptResponse:
    @classmethod
    def default(cls, ):
        return lambda: ReEncryptResponse_ReEncryptResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ReEncryptResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ReEncryptResponse_ReEncryptResponse)

class ReEncryptResponse_ReEncryptResponse(ReEncryptResponse, NamedTuple('ReEncryptResponse', [('CiphertextBlob', Any), ('SourceKeyId', Any), ('KeyId', Any), ('SourceEncryptionAlgorithm', Any), ('DestinationEncryptionAlgorithm', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ReEncryptResponse.ReEncryptResponse({_dafny.string_of(self.CiphertextBlob)}, {_dafny.string_of(self.SourceKeyId)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.SourceEncryptionAlgorithm)}, {_dafny.string_of(self.DestinationEncryptionAlgorithm)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ReEncryptResponse_ReEncryptResponse) and self.CiphertextBlob == __o.CiphertextBlob and self.SourceKeyId == __o.SourceKeyId and self.KeyId == __o.KeyId and self.SourceEncryptionAlgorithm == __o.SourceEncryptionAlgorithm and self.DestinationEncryptionAlgorithm == __o.DestinationEncryptionAlgorithm
    def __hash__(self) -> int:
        return super().__hash__()


class RegionType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class ReplicateKeyRequest:
    @classmethod
    def default(cls, ):
        return lambda: ReplicateKeyRequest_ReplicateKeyRequest(_dafny.Seq({}), _dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ReplicateKeyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ReplicateKeyRequest_ReplicateKeyRequest)

class ReplicateKeyRequest_ReplicateKeyRequest(ReplicateKeyRequest, NamedTuple('ReplicateKeyRequest', [('KeyId', Any), ('ReplicaRegion', Any), ('Policy', Any), ('BypassPolicyLockoutSafetyCheck', Any), ('Description', Any), ('Tags', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ReplicateKeyRequest.ReplicateKeyRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.ReplicaRegion)}, {_dafny.string_of(self.Policy)}, {_dafny.string_of(self.BypassPolicyLockoutSafetyCheck)}, {_dafny.string_of(self.Description)}, {_dafny.string_of(self.Tags)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ReplicateKeyRequest_ReplicateKeyRequest) and self.KeyId == __o.KeyId and self.ReplicaRegion == __o.ReplicaRegion and self.Policy == __o.Policy and self.BypassPolicyLockoutSafetyCheck == __o.BypassPolicyLockoutSafetyCheck and self.Description == __o.Description and self.Tags == __o.Tags
    def __hash__(self) -> int:
        return super().__hash__()


class ReplicateKeyResponse:
    @classmethod
    def default(cls, ):
        return lambda: ReplicateKeyResponse_ReplicateKeyResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ReplicateKeyResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ReplicateKeyResponse_ReplicateKeyResponse)

class ReplicateKeyResponse_ReplicateKeyResponse(ReplicateKeyResponse, NamedTuple('ReplicateKeyResponse', [('ReplicaKeyMetadata', Any), ('ReplicaPolicy', Any), ('ReplicaTags', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ReplicateKeyResponse.ReplicateKeyResponse({_dafny.string_of(self.ReplicaKeyMetadata)}, {_dafny.string_of(self.ReplicaPolicy)}, {_dafny.string_of(self.ReplicaTags)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ReplicateKeyResponse_ReplicateKeyResponse) and self.ReplicaKeyMetadata == __o.ReplicaKeyMetadata and self.ReplicaPolicy == __o.ReplicaPolicy and self.ReplicaTags == __o.ReplicaTags
    def __hash__(self) -> int:
        return super().__hash__()


class RetireGrantRequest:
    @classmethod
    def default(cls, ):
        return lambda: RetireGrantRequest_RetireGrantRequest(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_RetireGrantRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.RetireGrantRequest_RetireGrantRequest)

class RetireGrantRequest_RetireGrantRequest(RetireGrantRequest, NamedTuple('RetireGrantRequest', [('GrantToken', Any), ('KeyId', Any), ('GrantId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.RetireGrantRequest.RetireGrantRequest({_dafny.string_of(self.GrantToken)}, {_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.GrantId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.RetireGrantRequest_RetireGrantRequest) and self.GrantToken == __o.GrantToken and self.KeyId == __o.KeyId and self.GrantId == __o.GrantId
    def __hash__(self) -> int:
        return super().__hash__()


class RevokeGrantRequest:
    @classmethod
    def default(cls, ):
        return lambda: RevokeGrantRequest_RevokeGrantRequest(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_RevokeGrantRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.RevokeGrantRequest_RevokeGrantRequest)

class RevokeGrantRequest_RevokeGrantRequest(RevokeGrantRequest, NamedTuple('RevokeGrantRequest', [('KeyId', Any), ('GrantId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.RevokeGrantRequest.RevokeGrantRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.GrantId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.RevokeGrantRequest_RevokeGrantRequest) and self.KeyId == __o.KeyId and self.GrantId == __o.GrantId
    def __hash__(self) -> int:
        return super().__hash__()


class ScheduleKeyDeletionRequest:
    @classmethod
    def default(cls, ):
        return lambda: ScheduleKeyDeletionRequest_ScheduleKeyDeletionRequest(_dafny.Seq({}), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ScheduleKeyDeletionRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ScheduleKeyDeletionRequest_ScheduleKeyDeletionRequest)

class ScheduleKeyDeletionRequest_ScheduleKeyDeletionRequest(ScheduleKeyDeletionRequest, NamedTuple('ScheduleKeyDeletionRequest', [('KeyId', Any), ('PendingWindowInDays', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ScheduleKeyDeletionRequest.ScheduleKeyDeletionRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.PendingWindowInDays)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ScheduleKeyDeletionRequest_ScheduleKeyDeletionRequest) and self.KeyId == __o.KeyId and self.PendingWindowInDays == __o.PendingWindowInDays
    def __hash__(self) -> int:
        return super().__hash__()


class ScheduleKeyDeletionResponse:
    @classmethod
    def default(cls, ):
        return lambda: ScheduleKeyDeletionResponse_ScheduleKeyDeletionResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ScheduleKeyDeletionResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.ScheduleKeyDeletionResponse_ScheduleKeyDeletionResponse)

class ScheduleKeyDeletionResponse_ScheduleKeyDeletionResponse(ScheduleKeyDeletionResponse, NamedTuple('ScheduleKeyDeletionResponse', [('KeyId', Any), ('DeletionDate', Any), ('KeyState', Any), ('PendingWindowInDays', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.ScheduleKeyDeletionResponse.ScheduleKeyDeletionResponse({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.DeletionDate)}, {_dafny.string_of(self.KeyState)}, {_dafny.string_of(self.PendingWindowInDays)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.ScheduleKeyDeletionResponse_ScheduleKeyDeletionResponse) and self.KeyId == __o.KeyId and self.DeletionDate == __o.DeletionDate and self.KeyState == __o.KeyState and self.PendingWindowInDays == __o.PendingWindowInDays
    def __hash__(self) -> int:
        return super().__hash__()


class SigningAlgorithmSpec:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [SigningAlgorithmSpec_RSASSA__PSS__SHA__256(), SigningAlgorithmSpec_RSASSA__PSS__SHA__384(), SigningAlgorithmSpec_RSASSA__PSS__SHA__512(), SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256(), SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384(), SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512(), SigningAlgorithmSpec_ECDSA__SHA__256(), SigningAlgorithmSpec_ECDSA__SHA__384(), SigningAlgorithmSpec_ECDSA__SHA__512()]
    @classmethod
    def default(cls, ):
        return lambda: SigningAlgorithmSpec_RSASSA__PSS__SHA__256()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_RSASSA__PSS__SHA__256(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PSS__SHA__256)
    @property
    def is_RSASSA__PSS__SHA__384(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PSS__SHA__384)
    @property
    def is_RSASSA__PSS__SHA__512(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PSS__SHA__512)
    @property
    def is_RSASSA__PKCS1__V1__5__SHA__256(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256)
    @property
    def is_RSASSA__PKCS1__V1__5__SHA__384(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384)
    @property
    def is_RSASSA__PKCS1__V1__5__SHA__512(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512)
    @property
    def is_ECDSA__SHA__256(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_ECDSA__SHA__256)
    @property
    def is_ECDSA__SHA__384(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_ECDSA__SHA__384)
    @property
    def is_ECDSA__SHA__512(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_ECDSA__SHA__512)

class SigningAlgorithmSpec_RSASSA__PSS__SHA__256(SigningAlgorithmSpec, NamedTuple('RSASSA__PSS__SHA__256', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SigningAlgorithmSpec.RSASSA_PSS_SHA_256'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PSS__SHA__256)
    def __hash__(self) -> int:
        return super().__hash__()

class SigningAlgorithmSpec_RSASSA__PSS__SHA__384(SigningAlgorithmSpec, NamedTuple('RSASSA__PSS__SHA__384', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SigningAlgorithmSpec.RSASSA_PSS_SHA_384'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PSS__SHA__384)
    def __hash__(self) -> int:
        return super().__hash__()

class SigningAlgorithmSpec_RSASSA__PSS__SHA__512(SigningAlgorithmSpec, NamedTuple('RSASSA__PSS__SHA__512', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SigningAlgorithmSpec.RSASSA_PSS_SHA_512'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PSS__SHA__512)
    def __hash__(self) -> int:
        return super().__hash__()

class SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256(SigningAlgorithmSpec, NamedTuple('RSASSA__PKCS1__V1__5__SHA__256', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_256'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__256)
    def __hash__(self) -> int:
        return super().__hash__()

class SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384(SigningAlgorithmSpec, NamedTuple('RSASSA__PKCS1__V1__5__SHA__384', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_384'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__384)
    def __hash__(self) -> int:
        return super().__hash__()

class SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512(SigningAlgorithmSpec, NamedTuple('RSASSA__PKCS1__V1__5__SHA__512', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SigningAlgorithmSpec.RSASSA_PKCS1_V1_5_SHA_512'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_RSASSA__PKCS1__V1__5__SHA__512)
    def __hash__(self) -> int:
        return super().__hash__()

class SigningAlgorithmSpec_ECDSA__SHA__256(SigningAlgorithmSpec, NamedTuple('ECDSA__SHA__256', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SigningAlgorithmSpec.ECDSA_SHA_256'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_ECDSA__SHA__256)
    def __hash__(self) -> int:
        return super().__hash__()

class SigningAlgorithmSpec_ECDSA__SHA__384(SigningAlgorithmSpec, NamedTuple('ECDSA__SHA__384', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SigningAlgorithmSpec.ECDSA_SHA_384'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_ECDSA__SHA__384)
    def __hash__(self) -> int:
        return super().__hash__()

class SigningAlgorithmSpec_ECDSA__SHA__512(SigningAlgorithmSpec, NamedTuple('ECDSA__SHA__512', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SigningAlgorithmSpec.ECDSA_SHA_512'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec_ECDSA__SHA__512)
    def __hash__(self) -> int:
        return super().__hash__()


class SignRequest:
    @classmethod
    def default(cls, ):
        return lambda: SignRequest_SignRequest(_dafny.Seq({}), _dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SignRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SignRequest_SignRequest)

class SignRequest_SignRequest(SignRequest, NamedTuple('SignRequest', [('KeyId', Any), ('Message', Any), ('MessageType', Any), ('GrantTokens', Any), ('SigningAlgorithm', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SignRequest.SignRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Message)}, {_dafny.string_of(self.MessageType)}, {_dafny.string_of(self.GrantTokens)}, {_dafny.string_of(self.SigningAlgorithm)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SignRequest_SignRequest) and self.KeyId == __o.KeyId and self.Message == __o.Message and self.MessageType == __o.MessageType and self.GrantTokens == __o.GrantTokens and self.SigningAlgorithm == __o.SigningAlgorithm
    def __hash__(self) -> int:
        return super().__hash__()


class SignResponse:
    @classmethod
    def default(cls, ):
        return lambda: SignResponse_SignResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SignResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.SignResponse_SignResponse)

class SignResponse_SignResponse(SignResponse, NamedTuple('SignResponse', [('KeyId', Any), ('Signature', Any), ('SigningAlgorithm', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.SignResponse.SignResponse({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Signature)}, {_dafny.string_of(self.SigningAlgorithm)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.SignResponse_SignResponse) and self.KeyId == __o.KeyId and self.Signature == __o.Signature and self.SigningAlgorithm == __o.SigningAlgorithm
    def __hash__(self) -> int:
        return super().__hash__()


class Tag:
    @classmethod
    def default(cls, ):
        return lambda: Tag_Tag(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Tag(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Tag_Tag)

class Tag_Tag(Tag, NamedTuple('Tag', [('TagKey', Any), ('TagValue', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Tag.Tag({_dafny.string_of(self.TagKey)}, {_dafny.string_of(self.TagValue)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Tag_Tag) and self.TagKey == __o.TagKey and self.TagValue == __o.TagValue
    def __hash__(self) -> int:
        return super().__hash__()


class TagKeyType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class TagResourceRequest:
    @classmethod
    def default(cls, ):
        return lambda: TagResourceRequest_TagResourceRequest(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_TagResourceRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.TagResourceRequest_TagResourceRequest)

class TagResourceRequest_TagResourceRequest(TagResourceRequest, NamedTuple('TagResourceRequest', [('KeyId', Any), ('Tags', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.TagResourceRequest.TagResourceRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Tags)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.TagResourceRequest_TagResourceRequest) and self.KeyId == __o.KeyId and self.Tags == __o.Tags
    def __hash__(self) -> int:
        return super().__hash__()


class TagValueType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class IKMSClientCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "ComAmazonawsKmsTypes.IKMSClientCallHistory"

class IKMSClient:
    pass
    def CancelKeyDeletion(self, input):
        pass

    def ConnectCustomKeyStore(self, input):
        pass

    def CreateAlias(self, input):
        pass

    def CreateCustomKeyStore(self, input):
        pass

    def CreateGrant(self, input):
        pass

    def CreateKey(self, input):
        pass

    def Decrypt(self, input):
        pass

    def DeleteAlias(self, input):
        pass

    def DeleteCustomKeyStore(self, input):
        pass

    def DeleteImportedKeyMaterial(self, input):
        pass

    def DescribeCustomKeyStores(self, input):
        pass

    def DescribeKey(self, input):
        pass

    def DisableKey(self, input):
        pass

    def DisableKeyRotation(self, input):
        pass

    def DisconnectCustomKeyStore(self, input):
        pass

    def EnableKey(self, input):
        pass

    def EnableKeyRotation(self, input):
        pass

    def Encrypt(self, input):
        pass

    def GenerateDataKey(self, input):
        pass

    def GenerateDataKeyPair(self, input):
        pass

    def GenerateDataKeyPairWithoutPlaintext(self, input):
        pass

    def GenerateDataKeyWithoutPlaintext(self, input):
        pass

    def GenerateRandom(self, input):
        pass

    def GetKeyPolicy(self, input):
        pass

    def GetKeyRotationStatus(self, input):
        pass

    def GetParametersForImport(self, input):
        pass

    def GetPublicKey(self, input):
        pass

    def ImportKeyMaterial(self, input):
        pass

    def ListAliases(self, input):
        pass

    def ListGrants(self, input):
        pass

    def ListKeyPolicies(self, input):
        pass

    def ListResourceTags(self, input):
        pass

    def PutKeyPolicy(self, input):
        pass

    def ReEncrypt(self, input):
        pass

    def ReplicateKey(self, input):
        pass

    def RetireGrant(self, input):
        pass

    def RevokeGrant(self, input):
        pass

    def ScheduleKeyDeletion(self, input):
        pass

    def Sign(self, input):
        pass

    def TagResource(self, input):
        pass

    def UntagResource(self, input):
        pass

    def UpdateAlias(self, input):
        pass

    def UpdateCustomKeyStore(self, input):
        pass

    def UpdateKeyDescription(self, input):
        pass

    def UpdatePrimaryRegion(self, input):
        pass

    def Verify(self, input):
        pass


class TrentServiceConfig:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [TrentServiceConfig_TrentServiceConfig()]
    @classmethod
    def default(cls, ):
        return lambda: TrentServiceConfig_TrentServiceConfig()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_TrentServiceConfig(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.TrentServiceConfig_TrentServiceConfig)

class TrentServiceConfig_TrentServiceConfig(TrentServiceConfig, NamedTuple('TrentServiceConfig', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.TrentServiceConfig.TrentServiceConfig'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.TrentServiceConfig_TrentServiceConfig)
    def __hash__(self) -> int:
        return super().__hash__()


class TrustAnchorCertificateType:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class UntagResourceRequest:
    @classmethod
    def default(cls, ):
        return lambda: UntagResourceRequest_UntagResourceRequest(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UntagResourceRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.UntagResourceRequest_UntagResourceRequest)

class UntagResourceRequest_UntagResourceRequest(UntagResourceRequest, NamedTuple('UntagResourceRequest', [('KeyId', Any), ('TagKeys', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.UntagResourceRequest.UntagResourceRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.TagKeys)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.UntagResourceRequest_UntagResourceRequest) and self.KeyId == __o.KeyId and self.TagKeys == __o.TagKeys
    def __hash__(self) -> int:
        return super().__hash__()


class UpdateAliasRequest:
    @classmethod
    def default(cls, ):
        return lambda: UpdateAliasRequest_UpdateAliasRequest(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UpdateAliasRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.UpdateAliasRequest_UpdateAliasRequest)

class UpdateAliasRequest_UpdateAliasRequest(UpdateAliasRequest, NamedTuple('UpdateAliasRequest', [('AliasName', Any), ('TargetKeyId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.UpdateAliasRequest.UpdateAliasRequest({_dafny.string_of(self.AliasName)}, {_dafny.string_of(self.TargetKeyId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.UpdateAliasRequest_UpdateAliasRequest) and self.AliasName == __o.AliasName and self.TargetKeyId == __o.TargetKeyId
    def __hash__(self) -> int:
        return super().__hash__()


class UpdateCustomKeyStoreRequest:
    @classmethod
    def default(cls, ):
        return lambda: UpdateCustomKeyStoreRequest_UpdateCustomKeyStoreRequest(_dafny.Seq({}), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UpdateCustomKeyStoreRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.UpdateCustomKeyStoreRequest_UpdateCustomKeyStoreRequest)

class UpdateCustomKeyStoreRequest_UpdateCustomKeyStoreRequest(UpdateCustomKeyStoreRequest, NamedTuple('UpdateCustomKeyStoreRequest', [('CustomKeyStoreId', Any), ('NewCustomKeyStoreName', Any), ('KeyStorePassword', Any), ('CloudHsmClusterId', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.UpdateCustomKeyStoreRequest.UpdateCustomKeyStoreRequest({_dafny.string_of(self.CustomKeyStoreId)}, {_dafny.string_of(self.NewCustomKeyStoreName)}, {_dafny.string_of(self.KeyStorePassword)}, {_dafny.string_of(self.CloudHsmClusterId)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.UpdateCustomKeyStoreRequest_UpdateCustomKeyStoreRequest) and self.CustomKeyStoreId == __o.CustomKeyStoreId and self.NewCustomKeyStoreName == __o.NewCustomKeyStoreName and self.KeyStorePassword == __o.KeyStorePassword and self.CloudHsmClusterId == __o.CloudHsmClusterId
    def __hash__(self) -> int:
        return super().__hash__()


class UpdateCustomKeyStoreResponse:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [UpdateCustomKeyStoreResponse_UpdateCustomKeyStoreResponse()]
    @classmethod
    def default(cls, ):
        return lambda: UpdateCustomKeyStoreResponse_UpdateCustomKeyStoreResponse()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UpdateCustomKeyStoreResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.UpdateCustomKeyStoreResponse_UpdateCustomKeyStoreResponse)

class UpdateCustomKeyStoreResponse_UpdateCustomKeyStoreResponse(UpdateCustomKeyStoreResponse, NamedTuple('UpdateCustomKeyStoreResponse', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.UpdateCustomKeyStoreResponse.UpdateCustomKeyStoreResponse'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.UpdateCustomKeyStoreResponse_UpdateCustomKeyStoreResponse)
    def __hash__(self) -> int:
        return super().__hash__()


class UpdateKeyDescriptionRequest:
    @classmethod
    def default(cls, ):
        return lambda: UpdateKeyDescriptionRequest_UpdateKeyDescriptionRequest(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UpdateKeyDescriptionRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.UpdateKeyDescriptionRequest_UpdateKeyDescriptionRequest)

class UpdateKeyDescriptionRequest_UpdateKeyDescriptionRequest(UpdateKeyDescriptionRequest, NamedTuple('UpdateKeyDescriptionRequest', [('KeyId', Any), ('Description', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.UpdateKeyDescriptionRequest.UpdateKeyDescriptionRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Description)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.UpdateKeyDescriptionRequest_UpdateKeyDescriptionRequest) and self.KeyId == __o.KeyId and self.Description == __o.Description
    def __hash__(self) -> int:
        return super().__hash__()


class UpdatePrimaryRegionRequest:
    @classmethod
    def default(cls, ):
        return lambda: UpdatePrimaryRegionRequest_UpdatePrimaryRegionRequest(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UpdatePrimaryRegionRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.UpdatePrimaryRegionRequest_UpdatePrimaryRegionRequest)

class UpdatePrimaryRegionRequest_UpdatePrimaryRegionRequest(UpdatePrimaryRegionRequest, NamedTuple('UpdatePrimaryRegionRequest', [('KeyId', Any), ('PrimaryRegion', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.UpdatePrimaryRegionRequest.UpdatePrimaryRegionRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.PrimaryRegion)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.UpdatePrimaryRegionRequest_UpdatePrimaryRegionRequest) and self.KeyId == __o.KeyId and self.PrimaryRegion == __o.PrimaryRegion
    def __hash__(self) -> int:
        return super().__hash__()


class VerifyRequest:
    @classmethod
    def default(cls, ):
        return lambda: VerifyRequest_VerifyRequest(_dafny.Seq({}), _dafny.Seq({}), Wrappers.Option.default()(), _dafny.Seq({}), software_amazon_cryptography_services_kms_internaldafny_types.SigningAlgorithmSpec.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_VerifyRequest(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.VerifyRequest_VerifyRequest)

class VerifyRequest_VerifyRequest(VerifyRequest, NamedTuple('VerifyRequest', [('KeyId', Any), ('Message', Any), ('MessageType', Any), ('Signature', Any), ('SigningAlgorithm', Any), ('GrantTokens', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.VerifyRequest.VerifyRequest({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.Message)}, {_dafny.string_of(self.MessageType)}, {_dafny.string_of(self.Signature)}, {_dafny.string_of(self.SigningAlgorithm)}, {_dafny.string_of(self.GrantTokens)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.VerifyRequest_VerifyRequest) and self.KeyId == __o.KeyId and self.Message == __o.Message and self.MessageType == __o.MessageType and self.Signature == __o.Signature and self.SigningAlgorithm == __o.SigningAlgorithm and self.GrantTokens == __o.GrantTokens
    def __hash__(self) -> int:
        return super().__hash__()


class VerifyResponse:
    @classmethod
    def default(cls, ):
        return lambda: VerifyResponse_VerifyResponse(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_VerifyResponse(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.VerifyResponse_VerifyResponse)

class VerifyResponse_VerifyResponse(VerifyResponse, NamedTuple('VerifyResponse', [('KeyId', Any), ('SignatureValid', Any), ('SigningAlgorithm', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.VerifyResponse.VerifyResponse({_dafny.string_of(self.KeyId)}, {_dafny.string_of(self.SignatureValid)}, {_dafny.string_of(self.SigningAlgorithm)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.VerifyResponse_VerifyResponse) and self.KeyId == __o.KeyId and self.SignatureValid == __o.SignatureValid and self.SigningAlgorithm == __o.SigningAlgorithm
    def __hash__(self) -> int:
        return super().__hash__()


class WrappingKeySpec:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [WrappingKeySpec_RSA__2048()]
    @classmethod
    def default(cls, ):
        return lambda: WrappingKeySpec_RSA__2048()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_RSA__2048(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.WrappingKeySpec_RSA__2048)

class WrappingKeySpec_RSA__2048(WrappingKeySpec, NamedTuple('RSA__2048', [])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.WrappingKeySpec.RSA_2048'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.WrappingKeySpec_RSA__2048)
    def __hash__(self) -> int:
        return super().__hash__()


class Error:
    @classmethod
    def default(cls, ):
        return lambda: Error_AlreadyExistsException(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_AlreadyExistsException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_AlreadyExistsException)
    @property
    def is_CloudHsmClusterInUseException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterInUseException)
    @property
    def is_CloudHsmClusterInvalidConfigurationException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterInvalidConfigurationException)
    @property
    def is_CloudHsmClusterNotActiveException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterNotActiveException)
    @property
    def is_CloudHsmClusterNotFoundException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterNotFoundException)
    @property
    def is_CloudHsmClusterNotRelatedException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterNotRelatedException)
    @property
    def is_CustomKeyStoreHasCMKsException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_CustomKeyStoreHasCMKsException)
    @property
    def is_CustomKeyStoreInvalidStateException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_CustomKeyStoreInvalidStateException)
    @property
    def is_CustomKeyStoreNameInUseException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_CustomKeyStoreNameInUseException)
    @property
    def is_CustomKeyStoreNotFoundException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_CustomKeyStoreNotFoundException)
    @property
    def is_DependencyTimeoutException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_DependencyTimeoutException)
    @property
    def is_DisabledException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_DisabledException)
    @property
    def is_ExpiredImportTokenException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_ExpiredImportTokenException)
    @property
    def is_IncorrectKeyException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_IncorrectKeyException)
    @property
    def is_IncorrectKeyMaterialException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_IncorrectKeyMaterialException)
    @property
    def is_IncorrectTrustAnchorException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_IncorrectTrustAnchorException)
    @property
    def is_InvalidAliasNameException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidAliasNameException)
    @property
    def is_InvalidArnException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidArnException)
    @property
    def is_InvalidCiphertextException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidCiphertextException)
    @property
    def is_InvalidGrantIdException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidGrantIdException)
    @property
    def is_InvalidGrantTokenException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidGrantTokenException)
    @property
    def is_InvalidImportTokenException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidImportTokenException)
    @property
    def is_InvalidKeyUsageException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidKeyUsageException)
    @property
    def is_InvalidMarkerException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidMarkerException)
    @property
    def is_KeyUnavailableException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_KeyUnavailableException)
    @property
    def is_KMSInternalException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_KMSInternalException)
    @property
    def is_KMSInvalidSignatureException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_KMSInvalidSignatureException)
    @property
    def is_KMSInvalidStateException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_KMSInvalidStateException)
    @property
    def is_LimitExceededException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_LimitExceededException)
    @property
    def is_MalformedPolicyDocumentException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_MalformedPolicyDocumentException)
    @property
    def is_NotFoundException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_NotFoundException)
    @property
    def is_TagException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_TagException)
    @property
    def is_UnsupportedOperationException(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_UnsupportedOperationException)
    @property
    def is_Opaque(self) -> bool:
        return isinstance(self, software_amazon_cryptography_services_kms_internaldafny_types.Error_Opaque)

class Error_AlreadyExistsException(Error, NamedTuple('AlreadyExistsException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.AlreadyExistsException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_AlreadyExistsException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CloudHsmClusterInUseException(Error, NamedTuple('CloudHsmClusterInUseException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.CloudHsmClusterInUseException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterInUseException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CloudHsmClusterInvalidConfigurationException(Error, NamedTuple('CloudHsmClusterInvalidConfigurationException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.CloudHsmClusterInvalidConfigurationException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterInvalidConfigurationException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CloudHsmClusterNotActiveException(Error, NamedTuple('CloudHsmClusterNotActiveException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.CloudHsmClusterNotActiveException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterNotActiveException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CloudHsmClusterNotFoundException(Error, NamedTuple('CloudHsmClusterNotFoundException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.CloudHsmClusterNotFoundException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterNotFoundException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CloudHsmClusterNotRelatedException(Error, NamedTuple('CloudHsmClusterNotRelatedException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.CloudHsmClusterNotRelatedException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_CloudHsmClusterNotRelatedException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CustomKeyStoreHasCMKsException(Error, NamedTuple('CustomKeyStoreHasCMKsException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.CustomKeyStoreHasCMKsException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_CustomKeyStoreHasCMKsException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CustomKeyStoreInvalidStateException(Error, NamedTuple('CustomKeyStoreInvalidStateException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.CustomKeyStoreInvalidStateException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_CustomKeyStoreInvalidStateException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CustomKeyStoreNameInUseException(Error, NamedTuple('CustomKeyStoreNameInUseException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.CustomKeyStoreNameInUseException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_CustomKeyStoreNameInUseException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CustomKeyStoreNotFoundException(Error, NamedTuple('CustomKeyStoreNotFoundException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.CustomKeyStoreNotFoundException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_CustomKeyStoreNotFoundException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_DependencyTimeoutException(Error, NamedTuple('DependencyTimeoutException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.DependencyTimeoutException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_DependencyTimeoutException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_DisabledException(Error, NamedTuple('DisabledException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.DisabledException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_DisabledException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_ExpiredImportTokenException(Error, NamedTuple('ExpiredImportTokenException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.ExpiredImportTokenException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_ExpiredImportTokenException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_IncorrectKeyException(Error, NamedTuple('IncorrectKeyException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.IncorrectKeyException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_IncorrectKeyException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_IncorrectKeyMaterialException(Error, NamedTuple('IncorrectKeyMaterialException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.IncorrectKeyMaterialException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_IncorrectKeyMaterialException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_IncorrectTrustAnchorException(Error, NamedTuple('IncorrectTrustAnchorException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.IncorrectTrustAnchorException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_IncorrectTrustAnchorException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_InvalidAliasNameException(Error, NamedTuple('InvalidAliasNameException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.InvalidAliasNameException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidAliasNameException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_InvalidArnException(Error, NamedTuple('InvalidArnException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.InvalidArnException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidArnException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_InvalidCiphertextException(Error, NamedTuple('InvalidCiphertextException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.InvalidCiphertextException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidCiphertextException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_InvalidGrantIdException(Error, NamedTuple('InvalidGrantIdException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.InvalidGrantIdException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidGrantIdException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_InvalidGrantTokenException(Error, NamedTuple('InvalidGrantTokenException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.InvalidGrantTokenException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidGrantTokenException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_InvalidImportTokenException(Error, NamedTuple('InvalidImportTokenException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.InvalidImportTokenException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidImportTokenException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_InvalidKeyUsageException(Error, NamedTuple('InvalidKeyUsageException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.InvalidKeyUsageException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidKeyUsageException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_InvalidMarkerException(Error, NamedTuple('InvalidMarkerException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.InvalidMarkerException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidMarkerException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_KeyUnavailableException(Error, NamedTuple('KeyUnavailableException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.KeyUnavailableException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_KeyUnavailableException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_KMSInternalException(Error, NamedTuple('KMSInternalException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.KMSInternalException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_KMSInternalException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_KMSInvalidSignatureException(Error, NamedTuple('KMSInvalidSignatureException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.KMSInvalidSignatureException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_KMSInvalidSignatureException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_KMSInvalidStateException(Error, NamedTuple('KMSInvalidStateException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.KMSInvalidStateException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_KMSInvalidStateException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_LimitExceededException(Error, NamedTuple('LimitExceededException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.LimitExceededException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_LimitExceededException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_MalformedPolicyDocumentException(Error, NamedTuple('MalformedPolicyDocumentException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.MalformedPolicyDocumentException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_MalformedPolicyDocumentException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_NotFoundException(Error, NamedTuple('NotFoundException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.NotFoundException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_NotFoundException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_TagException(Error, NamedTuple('TagException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.TagException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_TagException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_UnsupportedOperationException(Error, NamedTuple('UnsupportedOperationException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.UnsupportedOperationException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_UnsupportedOperationException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_Opaque(Error, NamedTuple('Opaque', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'ComAmazonawsKmsTypes.Error.Opaque({_dafny.string_of(self.obj)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, software_amazon_cryptography_services_kms_internaldafny_types.Error_Opaque) and self.obj == __o.obj
    def __hash__(self) -> int:
        return super().__hash__()


class OpaqueError:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return software_amazon_cryptography_services_kms_internaldafny_types.Error.default()()
