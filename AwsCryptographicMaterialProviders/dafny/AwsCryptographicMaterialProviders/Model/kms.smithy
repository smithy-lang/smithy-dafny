namespace aws.cryptography.materialProviders

use aws.polymorph#reference
use aws.polymorph#positional
use aws.polymorph#extendable
use aws.polymorph#javadoc

use com.amazonaws.kms#TrentService

///////////////////
// Basic structures

string KmsKeyId

list KmsKeyIdList {
  member: KmsKeyId
}

string Region

list RegionList {
  member: Region
}

string AccountId

list AccountIdList {
  member: AccountId
}

//////////
// Clients

@reference(service: TrentService)
structure KmsClientReference {}

///////////////////
// Client Suppliers

@extendable
resource ClientSupplier {
  operations: [GetClient],
}

@reference(resource: ClientSupplier)
structure ClientSupplierReference {}

@javadoc("Returns an AWS KMS Client.")
operation GetClient {
  input: GetClientInput,
  output: GetClientOutput,
}

@javadoc("Inputs for getting a AWS KMS Client.")
structure GetClientInput {
  @required
  @javadoc("The region the client should be created in.")
  region: Region,
}

@positional
structure GetClientOutput {
  @required
  client: KmsClientReference,
}

operation CreateDefaultClientSupplier {
  input: CreateDefaultClientSupplierInput,
  output: CreateDefaultClientSupplierOutput
}

structure CreateDefaultClientSupplierInput {
}

@positional
structure CreateDefaultClientSupplierOutput {
  @required
  client: ClientSupplierReference
}
