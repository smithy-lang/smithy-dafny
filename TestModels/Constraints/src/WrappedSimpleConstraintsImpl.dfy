include "../Model/SimpleConstraintsTypesWrapped.dfy"

module {:extern "simple.constraints.internaldafny.wrapped"} WrappedSimpleConstraintsService refines WrappedAbstractSimpleConstraintsService {
    import WrappedService = SimpleConstraints
    function method WrappedDefaultSimpleConstraintsConfig(): SimpleConstraintsConfig {
        SimpleConstraintsConfig
    }
}
