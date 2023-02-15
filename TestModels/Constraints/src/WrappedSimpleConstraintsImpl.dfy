include "../Model/SimpleConstraintsTypesWrapped.dfy"

module {:extern "Dafny.Simple.Constraints.Wrapped"} WrappedSimpleConstraintsService refines WrappedAbstractSimpleConstraintsService {
    import WrappedService = SimpleConstraints
    function method WrappedDefaultSimpleConstraintsConfig(): SimpleConstraintsConfig {
        SimpleConstraintsConfig
    }
}