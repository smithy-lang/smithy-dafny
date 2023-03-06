include "../Model/SimpleUnionTypesWrapped.dfy"

module {:extern "Dafny.Simple.Union.Wrapped"} WrappedSimpleUnionService refines WrappedAbstractSimpleUnionService {
    import WrappedService = SimpleUnion
    function method WrappedDefaultSimpleUnionConfig(): SimpleUnionConfig {
        SimpleUnionConfig
    }
}