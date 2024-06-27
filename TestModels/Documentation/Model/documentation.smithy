// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.documentation

/// A service that supports the operation of getting things.
@aws.polymorph#localService(
  sdkId: "SimpleDocumentation",
  config: SimpleDocumentationConfig,
)
service SimpleDocumentation {
  version: "2021-11-01",
  resources: [ Widget ],
  operations: [ GetThing ],
  errors: [ CouldntGetTheThingError ],
}

/// Fancy configuration things to make getting things even thingier.
structure SimpleDocumentationConfig {}

/// A thing that you can get from the service.
structure Thing {
  /// The name of the thing.
  name: String
}

/// Call this to get a thing.
operation GetThing {
  input: GetThingInput
  output: GetThingOutput
}

/// Inputs for getting a thing.
structure GetThingInput {
  /// The name of the thing to get, obviously.
  @required
  name: String
}

/// Outputs for getting a thing.
structure GetThingOutput {
  /// The thing that you just got.
  @required
  thing: Thing
}

/// A different kind of thing you can get.
resource Widget {
  operations: [ SetWidgetName ]
}

@aws.polymorph#reference(resource: Widget)
structure WidgetReference {}

operation SetWidgetName {
  input: SetWidgetNameInput
}

structure SetWidgetNameInput {
  @required
  name: String
}

/// Error returned when we couldn't get the thing.
@error("server")
structure CouldntGetTheThingError {
  /// Error message (this documentation is ignored!)
  @required
  message: String
}

/// Either kind of thing.
union SomeKindOfThing {
  thing: Thing
  widget: WidgetReference
}

/// Types of widgets you can get.
@enum([
  {
    name: "BLUE",
    value: "BLUE"
  },
  {
    name: "LARGE",
    value: "LARGE"
  },
  {
    name: "SQUISHY"
    value: "SQUISHY"
  }
])
string WidgetType