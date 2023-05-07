include "../Model/SimpleDafnyExternTypesWrapped.dfy"

module {:extern "simple.dafnyextern.internaldafny.wrapped"} WrappedSimpleExternService refines WrappedAbstractSimpleDafnyExternService {
    import WrappedService = SimpleExtern
    function method WrappedDefaultSimpleExternConfig(): SimpleExternConfig {
        WrappedService.DefaultSimpleExternConfig()
    }
}
