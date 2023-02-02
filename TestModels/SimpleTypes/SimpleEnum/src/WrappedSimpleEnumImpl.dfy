include "../Model/SimpleTypesEnumTypesWrapped.dfy"

module {:extern "Dafny.Simple.Types.Enum.Wrapped"} WrappedSimpleTypesEnumService refines WrappedAbstractSimpleTypesEnumService {
    import WrappedService = SimpleEnum
    function method WrappedDefaultSimpleEnumConfig(): SimpleEnumConfig {
        SimpleEnumConfig
    }
}