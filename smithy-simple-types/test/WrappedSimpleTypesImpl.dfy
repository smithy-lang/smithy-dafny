include "../Model/ExampleSimpletypesTypesWrapped.dfy"

module {:extern "Dafny.Example.Simpletypes.Wrapped"} WrappedSimpletypesService refines WrappedAbstractExampleSimpletypesService {
    import WrappedService = SimpleTypes
    function method WrappedDefaultEmptyConfig(): EmptyConfig {
        EmptyConfig
    }
}