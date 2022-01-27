// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

$version: "1.0"

namespace polymorph.demo

use aws.polymorph#reference

service StringLists {
    version: "2021-06-23",
    resources: [ListOfStrings],
    operations: [CreateArrayList]
}

operation CreateArrayList {
    input: CreateArrayListInput,
    output: CreateArrayListOutput
}
structure CreateArrayListInput {
    @documentation("Length of the list to create")
    @range(min: 0)
    length: Integer
}
structure CreateArrayListOutput {
    @required
    list: ListOfStringsReference
}

resource ListOfStrings {
    operations: [GetElement, SetElement]
}
@reference(resource: ListOfStrings)
structure ListOfStringsReference {}

@readonly
operation GetElement {
    input: GetElementInput,
    output: GetElementOutput,
    errors: [IndexOutOfBoundsException]
}
structure GetElementInput {
    @range(min: 0)
    @required
    index: Integer
}
structure GetElementOutput {
    @required
    value: String
}

operation SetElement {
    input: SetElementInput,
    errors: [IndexOutOfBoundsException]
}
structure SetElementInput {
    @range(min: 0)
    @required
    index: Integer,

    @required
    value: String
}

@error("client")
structure IndexOutOfBoundsException {
    @required
    message: String
}
