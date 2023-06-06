include "../Model/SimpleTypesSmithyLongTypesWrapped.dfy"

module {:extern "simple.types.smithylong.internaldafny.wrapped"} WrappedSimpleTypesLongService refines WrappedAbstractSimpleTypesSmithyLongService {
    import WrappedService = SimpleLong
    function method WrappedDefaultSimpleLongConfig(): SimpleLongConfig {
        SimpleLongConfig
    }
}
