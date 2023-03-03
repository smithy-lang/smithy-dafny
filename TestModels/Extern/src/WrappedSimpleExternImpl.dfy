include "../Model/SimpleExternTypesWrapped.dfy"

module {:extern "Dafny.Simple.Extern.Wrapped"} WrappedSimpleExternService refines WrappedAbstractSimpleExternService {
    import WrappedService = SimpleExtern
    function method WrappedDefaultSimpleExternConfig(): SimpleExternConfig {
        WrappedService.DefaultSimpleExternConfig()
    }
}