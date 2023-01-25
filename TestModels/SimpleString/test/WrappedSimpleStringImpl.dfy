include "../Model/SimpleTypesStringTypesWrapped.dfy"

module {:extern "Dafny.Simple.Types.String.Wrapped"} WrappedSimpleTypesStringService refines WrappedAbstractSimpleTypesStringService {
    import WrappedService = SimpleString
    function method WrappedDefaultSimpleStringConfig(): SimpleStringConfig {
        SimpleStringConfig
    }
}