include "../Model/SimpleErrorsTypesWrapped.dfy"

module {:extern "Dafny.Simple.Errors.Wrapped"} WrappedSimpleErrorsService refines WrappedAbstractSimpleErrorsService {
    import WrappedService = SimpleErrors
    function method WrappedDefaultSimpleErrorsConfig(): SimpleErrorsConfig {
        SimpleErrorsConfig
    }
}