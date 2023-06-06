include "../Model/SimpleTypesIntegerTypesWrapped.dfy"

module {:extern "simple.types.integer.internaldafny.wrapped"} WrappedSimpleTypesIntegerService refines WrappedAbstractSimpleTypesIntegerService {
    import WrappedService = SimpleInteger
    function method WrappedDefaultSimpleIntegerConfig(): SimpleIntegerConfig {
        SimpleIntegerConfig
    }
}
