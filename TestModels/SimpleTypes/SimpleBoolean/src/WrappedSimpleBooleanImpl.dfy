include "../Model/SimpleTypesBooleanTypesWrapped.dfy"

module {:extern "simple.types.boolean.internaldafny.wrapped"} WrappedSimpleTypesBooleanService refines WrappedAbstractSimpleTypesBooleanService {
    import WrappedService = SimpleBoolean
    function method WrappedDefaultSimpleBooleanConfig(): SimpleBooleanConfig {
        SimpleBooleanConfig
    }
}
