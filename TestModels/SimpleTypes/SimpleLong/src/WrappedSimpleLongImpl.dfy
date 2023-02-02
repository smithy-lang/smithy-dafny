include "../Model/SimpleTypesLongTypesWrapped.dfy"

module {:extern "Dafny.Simple.Types.Long.Wrapped"} WrappedSimpleTypesLongService refines WrappedAbstractSimpleTypesLongService {
    import WrappedService = SimpleLong
    function method WrappedDefaultSimpleLongConfig(): SimpleLongConfig {
        SimpleLongConfig
    }
}