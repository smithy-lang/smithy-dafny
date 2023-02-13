include "../Model/SimpleRefinementTypesWrapped.dfy"

module {:extern "Dafny.Simple.Refinement.Wrapped"} WrappedSimpleRefinementService refines WrappedAbstractSimpleRefinementService {
    import WrappedService = SimpleRefinement
    function method WrappedDefaultSimpleRefinementConfig(): SimpleRefinementConfig {
        SimpleRefinementConfig
    }
}