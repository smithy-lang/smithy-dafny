include "../Model/SimpleUnionTypesWrapped.dfy"

module {:extern "simple.union.internaldafny.wrapped"} WrappedSimpleUnionService refines WrappedAbstractSimpleUnionService {
    import WrappedService = SimpleUnion
    function method WrappedDefaultSimpleUnionConfig(): SimpleUnionConfig {
        SimpleUnionConfig
    }
}
