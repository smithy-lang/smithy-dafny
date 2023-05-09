include "../Model/SimpleTypesSmithyStringTypesWrapped.dfy"

module {:extern "simple.types.smithystring.internaldafny.wrapped"} WrappedSimpleTypesStringService refines WrappedAbstractSimpleTypesSmithyStringService {
    import WrappedService = SimpleString
    function method WrappedDefaultSimpleStringConfig(): SimpleStringConfig {
        SimpleStringConfig
    }
}
