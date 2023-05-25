include "../Model/SimpleErrorsTypesWrapped.dfy"

module {:extern "simple.errors.internaldafny.wrapped"} WrappedSimpleErrorsService refines WrappedAbstractSimpleErrorsService {
    import WrappedService = SimpleErrors
    function method WrappedDefaultSimpleErrorsConfig(): SimpleErrorsConfig {
        SimpleErrorsConfig
    }
}
