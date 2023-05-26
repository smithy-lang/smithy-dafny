include "../Model/SimpleDependenciesTypesWrapped.dfy"

module {:extern "simple.dependencies.internaldafny.wrapped"} WrappedSimpleDependenciesService refines WrappedAbstractSimpleDependenciesService {
    import WrappedService = SimpleDependencies
    function method WrappedDefaultSimpleDependenciesConfig(): SimpleDependenciesConfig {
        SimpleDependenciesConfig(
            simpleResourcesConfig := Some(SimpleResourcesTypes.SimpleResourcesConfig(
                name := "default"
            )),
            extendableResourceReference := None(),
            simpleConstraintsServiceReference := None(),
            specialString := Some("bw1and10")
        )
    }
}
