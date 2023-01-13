namespace example.simpletypes
use aws.polymorph#localService

@aws.polymorph#localService(
    sdkId: "SimpleTypes",
    config: EmptyConfig
)
service SimpleTypesService {
    operations: [
        GetString
    ],
    errors: [

    ]
}

structure EmptyConfig{}

operation GetString{
    input: GetStringInput,
    output: GetStringOutput
}
structure GetStringInput{
    stringValue: String
}

structure GetStringOutput{
    result: String
}

