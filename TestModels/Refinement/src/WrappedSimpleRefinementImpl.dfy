include "../Model/SimpleRefinementTypesWrapped.dfy"

module {:extern "simple.refinement.internaldafny.wrapped"} WrappedSimpleRefinementService refines WrappedAbstractSimpleRefinementService {
    import WrappedService = SimpleRefinement
    function method WrappedDefaultSimpleRefinementConfig(): SimpleRefinementConfig {
        SimpleRefinementConfig
    }
}
