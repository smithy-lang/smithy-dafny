include "../Model/SimpleTypesBooleanTypesWrapped.dfy"

module {:extern "Dafny.Simpletypes.Boolean.Wrapped"} WrappedSimpleTypesBooleanService refines WrappedAbstractSimpletypesBooleanService {
    import WrappedService = SimpleBoolean
    function method WrappedDefaultSimpleBooleanConfig(): SimpleBooleanConfig {
        SimpleBooleanConfig
    }
}