include "../Model/SimpleTypesSmithyEnumTypesWrapped.dfy"

module {:extern "simple.types.smithyenum.internaldafny.wrapped"} WrappedSimpleTypesEnumService refines WrappedAbstractSimpleTypesSmithyEnumService {
    import WrappedService = SimpleEnum
    function method WrappedDefaultSimpleEnumConfig(): SimpleEnumConfig {
        SimpleEnumConfig
    }
}
