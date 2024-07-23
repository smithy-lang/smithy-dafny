#![allow(non_snake_case)]
use simple_aggregate::types::*;
use simple_aggregate::*;
use std::collections::HashMap;

#[tokio::test]
async fn test_get_aggregate() {
    let stringList = ["Test"];
    let simpleStringMap = HashMap::from([("Test1".to_string(), "Success".to_string())]);
    let structureList = vec![StructureListElement::builder()
        .string_value("Test2")
        .integer_value(2)
        .build()];
    let simpleIntegerMap = HashMap::from([("Test3".to_string(), 3)]);
    let nestedStructure = NestedStructure::builder()
        .string_structure(StringStructure::builder().value("Nested").build())
        .build();
    let result = client()
        .get_aggregate()
        .simple_integer_map("Test3", 3)
        .simple_string_map("Test1", "Success")
        .simple_string_list("Test")
        .structure_list(
            StructureListElement::builder()
                .string_value("Test2")
                .integer_value(2)
                .build(),
        )
        .nested_structure(nestedStructure.clone())
        .send()
        .await;

    let output = result.unwrap();

    assert_eq!(output.simple_integer_map.unwrap(), simpleIntegerMap);
    assert_eq!(output.simple_string_map.unwrap(), simpleStringMap);
    assert_eq!(output.structure_list.unwrap(), structureList);
    assert_eq!(output.nested_structure.unwrap(), nestedStructure);
    assert_eq!(output.simple_string_list.unwrap(), stringList);
}

pub fn client() -> Client {
    let config = SimpleAggregateConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
