include "../Model/SimpleConstructorTypesWrapped.dfy"

module {:extern "simple.constructor.internaldafny.wrapped"} WrappedSimpleConstructorService refines WrappedAbstractSimpleConstructorService {
    import WrappedService = SimpleConstructor
    function method WrappedDefaultSimpleConstructorConfig(): SimpleConstructorConfig {
        WrappedService.DefaultSimpleConstructorConfig()
    }
}
