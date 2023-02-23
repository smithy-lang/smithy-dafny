include "../Model/SimpleConstructorTypesWrapped.dfy"

module {:extern "Dafny.Simple.Constructor.Wrapped"} WrappedSimpleConstructorService refines WrappedAbstractSimpleConstructorService {
    import WrappedService = SimpleConstructor
    function method WrappedDefaultSimpleConstructorConfig(): SimpleConstructorConfig {
        WrappedService.DefaultSimpleConstructorConfig()
    }
}