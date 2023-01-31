include "../Model/SimpleTypesBooleanTypesWrapped.dfy"

module {:extern "Dafny.Simple.Types.Boolean.Wrapped"} WrappedSimpleTypesBooleanService refines WrappedAbstractSimpleTypesBooleanService {
    import WrappedService = SimpleBoolean
    function method WrappedDefaultSimpleBooleanConfig(): SimpleBooleanConfig {
        SimpleBooleanConfig
    }
}