namespace simple.types.document

@aws.polymorph#localService(
  sdkId: "SimpleDocument",
  config: SimpleDocumentConfig,
)
service SimpleTypesDocument {
  version: "2021-11-01",
  resources: [],
  operations: [ GetDocument ],
  errors: [],
}

structure SimpleDocumentConfig {}

operation GetDocument {
  input: GetDocumentInput,
  output: GetDocumentOutput,
}

structure GetDocumentInput {
  value: Document
}

structure GetDocumentOutput {
  value: Document
}