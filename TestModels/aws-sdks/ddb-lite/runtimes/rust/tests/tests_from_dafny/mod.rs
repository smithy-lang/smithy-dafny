#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
use ddb_lite::implementation_from_dafny::*;

pub mod r#_TestDDBv2_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn BasicQueryTests() -> () {
            let mut attributeNameMap: ::dafny_runtime::Map<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            > = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("#bkid")) => (::dafny_runtime::string_utf16_of("branch-key-id")), (::dafny_runtime::string_utf16_of("#status")) => (::dafny_runtime::string_utf16_of("status"))];
            let mut attributeValueMap: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>> = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of(":bkid")) => (::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue::S {
                S: ::dafny_runtime::string_utf16_of("aws-kms-h")
              })), (::dafny_runtime::string_utf16_of(":status")) => (::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue::S {
                S: ::dafny_runtime::string_utf16_of("ACTIVE")
              }))];
            let mut queryInput: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryInput> = ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryInput::QueryInput {
            TableName: super::r#_TestDDBv2_Compile::_default::tableNameTest(),
            IndexName: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: super::r#_TestDDBv2_Compile::_default::secIndex()
                }),
            Select: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Select>>::None {}),
            AttributesToGet: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeNameList>::None {}),
            Limit: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::PositiveIntegerObject>::None {}),
            ConsistentRead: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {}),
            KeyConditions: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Condition>>>::None {}),
            QueryFilter: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Condition>>>::None {}),
            ConditionalOperator: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ConditionalOperator>>::None {}),
            ScanIndexForward: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {}),
            ExclusiveStartKey: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>>>::None {}),
            ReturnConsumedCapacity: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnConsumedCapacity>>::None {}),
            ProjectionExpression: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::None {}),
            FilterExpression: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::None {}),
            KeyConditionExpression: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("#status = :status and #bkid = :bkid")
                }),
            ExpressionAttributeNames: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::Some {
                  value: attributeNameMap.clone()
                }),
            ExpressionAttributeValues: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>>>::Some {
                  value: attributeValueMap.clone()
                })
          });
            super::r#_TestDDBv2_Compile::_default::BasicQueryTest(&queryInput);
            return ();
        }
        pub fn BasicGetTests() -> () {
            let mut Key2Get: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>> = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("branch-key-id")) => (::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue::S {
                S: ::dafny_runtime::string_utf16_of("aws-kms-h")
              })), (::dafny_runtime::string_utf16_of("version")) => (::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue::S {
                S: ::dafny_runtime::string_utf16_of("1")
              }))];
            let mut getInput: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::GetItemInput> = ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::GetItemInput::GetItemInput {
            TableName: super::r#_TestDDBv2_Compile::_default::tableNameTest(),
            Key: Key2Get.clone(),
            AttributesToGet: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeNameList>::None {}),
            ConsistentRead: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {}),
            ReturnConsumedCapacity: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnConsumedCapacity>>::None {}),
            ProjectionExpression: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::None {}),
            ExpressionAttributeNames: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::None {})
          });
            super::r#_TestDDBv2_Compile::_default::BasicGetTest(&getInput);
            return ();
        }
        pub fn BasicPutTests() -> () {
            let mut attributeValueMap: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>> = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("branch-key-id")) => (::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue::S {
                S: ::dafny_runtime::string_utf16_of("aws-kms-put-item")
              })), (::dafny_runtime::string_utf16_of("status")) => (::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue::S {
                S: ::dafny_runtime::string_utf16_of("ACTIVE")
              })), (::dafny_runtime::string_utf16_of("version")) => (::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue::S {
                S: ::dafny_runtime::string_utf16_of("version-1")
              }))];
            let mut putInput: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::PutItemInput> = ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::PutItemInput::PutItemInput {
            TableName: super::r#_TestDDBv2_Compile::_default::tableNameTest(),
            Item: attributeValueMap.clone(),
            Expected: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ExpectedAttributeValue>>>::None {}),
            ReturnValues: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue>>::None {}),
            ReturnConsumedCapacity: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnConsumedCapacity>>::None {}),
            ReturnItemCollectionMetrics: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnItemCollectionMetrics>>::None {}),
            ConditionalOperator: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ConditionalOperator>>::None {}),
            ConditionExpression: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::None {}),
            ExpressionAttributeNames: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::None {}),
            ExpressionAttributeValues: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>>>::None {})
          });
            super::r#_TestDDBv2_Compile::_default::BasicPutTest(&putInput);
            return ();
        }
        pub fn BatGetItemTests() -> () {
            let mut attributeNameBranchKey: ::dafny_runtime::Sequence<
                ::dafny_runtime::DafnyCharUTF16,
            > = ::dafny_runtime::string_utf16_of("branch-key-id");
            let mut attributeValueBranchKey: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue> = ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue::S {
            S: ::dafny_runtime::string_utf16_of("aws-kms-put-item")
          });
            let mut attributeNameVersion: ::dafny_runtime::Sequence<
                ::dafny_runtime::DafnyCharUTF16,
            > = ::dafny_runtime::string_utf16_of("version");
            let mut attributeValueVersion: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue> = ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue::S {
            S: ::dafny_runtime::string_utf16_of("version-1")
          });
            let mut key: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>> = ::dafny_runtime::map![(attributeNameBranchKey.clone()) => (attributeValueBranchKey.clone()), (attributeNameVersion.clone()) => (attributeValueVersion.clone())];
            let mut keys: super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::KeyList = ::dafny_runtime::seq![key.clone()];
            let mut keyAndAttributes: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::KeysAndAttributes> = ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::KeysAndAttributes::KeysAndAttributes {
            Keys: keys.clone(),
            AttributesToGet: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeNameList>::None {}),
            ConsistentRead: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {}),
            ProjectionExpression: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::None {}),
            ExpressionAttributeNames: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::None {})
          });
            let mut batchGetRequestMap: super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetRequestMap = ::dafny_runtime::map![(super::r#_TestDDBv2_Compile::_default::tableNameTest()) => (keyAndAttributes.clone())];
            let mut batchGetInput: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemInput> = ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemInput::BatchGetItemInput {
            RequestItems: batchGetRequestMap.clone(),
            ReturnConsumedCapacity: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnConsumedCapacity>>::None {})
          });
            super::r#_TestDDBv2_Compile::_default::BatchGetItemTest(&batchGetInput);
            return ();
        }
        pub fn BasicQueryTest(
            input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryInput>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny::_default::DynamoDBClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryOutput>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryOutput>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient::Query(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !matches!(
                (&ret.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            let mut queryOutput: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryOutput> = ret.read().value().clone();
            if !matches!(
                queryOutput.Items().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut queryItem: ::dafny_runtime::Sequence<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>>> = queryOutput.Items().value().clone();
            if !(::dafny_runtime::int!(0) < queryItem.cardinality()) {
                panic!("Halt")
            };
            let mut item: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>> = queryItem.get(&::dafny_runtime::int!(0));
            if !(item.clone().keys()
                == ::dafny_runtime::set! {::dafny_runtime::string_utf16_of("branch-key-id"), ::dafny_runtime::string_utf16_of("version"), ::dafny_runtime::string_utf16_of("create-time"), ::dafny_runtime::string_utf16_of("enc"), ::dafny_runtime::string_utf16_of("hierarchy-version"), ::dafny_runtime::string_utf16_of("status")})
            {
                panic!("Halt")
            };
            if !(item.clone().keys().cardinality() == item.clone().values().cardinality()) {
                panic!("Halt")
            };
            return ();
        }
        pub fn BasicGetTest(
            input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::GetItemInput>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny::_default::DynamoDBClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::GetItemOutput>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::GetItemOutput>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient::GetItem(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !matches!(
                (&ret.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            let mut itemOutput: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::GetItemOutput> = ret.read().value().clone();
            if !matches!(
                itemOutput.Item().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut item: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::AttributeValue>> = itemOutput.Item().value().clone();
            if !(item.clone().keys()
                == ::dafny_runtime::set! {::dafny_runtime::string_utf16_of("branch-key-id"), ::dafny_runtime::string_utf16_of("version"), ::dafny_runtime::string_utf16_of("create-time"), ::dafny_runtime::string_utf16_of("enc"), ::dafny_runtime::string_utf16_of("hierarchy-version"), ::dafny_runtime::string_utf16_of("status")})
            {
                panic!("Halt")
            };
            if !(item.clone().keys().cardinality() == item.clone().values().cardinality()) {
                panic!("Halt")
            };
            return ();
        }
        pub fn BasicPutTest(
            input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::PutItemInput>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny::_default::DynamoDBClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::PutItemOutput>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out5 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::PutItemOutput>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            _out5 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient::PutItem(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out5.read());
            if !matches!(
                (&ret.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            return ();
        }
        pub fn BatchGetItemTest(
            input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemInput>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out6 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            _out6 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny::_default::DynamoDBClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out6.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemOutput>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out7 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemOutput>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>>>>::new();
            _out7 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient::BatchGetItem(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out7.read());
            if matches!(
                (&ret.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Failure { .. }
            ) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "\n\t BatchGetItemTest Failed"
                    ))
                );
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of("\n\t"))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret.read()));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of("\n"))
                )
            };
            if !matches!(
                (&ret.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            return ();
        }
        pub fn tableNameTest() -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            ::dafny_runtime::string_utf16_of("TestTable")
        }
        pub fn secIndex() -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            ::dafny_runtime::string_utf16_of("Active-Keys")
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any> for super::r#_TestDDBv2_Compile::_default {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod _module {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn _Test__Main_() -> () {
            let mut success: bool = true;
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestDDBv2.BasicQueryTests: "#
                ))
            );
            super::r#_TestDDBv2_Compile::_default::BasicQueryTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestDDBv2.BasicGetTests: "#
                ))
            );
            super::r#_TestDDBv2_Compile::_default::BasicGetTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestDDBv2.BasicPutTests: "#
                ))
            );
            super::r#_TestDDBv2_Compile::_default::BasicPutTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestDDBv2.BatGetItemTests: "#
                ))
            );
            super::r#_TestDDBv2_Compile::_default::BatGetItemTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            if !success {
                panic!("Halt")
            };
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any> for super::_module::_default {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
fn main() {
    _module::_default::_Test__Main_();
}
