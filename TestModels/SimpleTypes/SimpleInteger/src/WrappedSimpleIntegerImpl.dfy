include "../Model/SimpleTypesIntegerTypesWrapped.dfy"

module {:extern "Dafny.Simple.Types.Integer.Wrapped"} WrappedSimpleTypesIntegerService refines WrappedAbstractSimpleTypesIntegerService {
    import WrappedService = SimpleInteger
    function method WrappedDefaultSimpleIntegerConfig(): SimpleIntegerConfig {
        SimpleIntegerConfig
    }
}