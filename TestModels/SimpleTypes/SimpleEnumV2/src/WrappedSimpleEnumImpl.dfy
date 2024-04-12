include "../Model/SimpleTypesEnumV2TypesWrapped.dfy"

module {:extern "simple.types.enumv2.internaldafny.wrapped"} WrappedSimpleTypesEnumV2Service refines WrappedAbstractSimpleTypesEnumV2Service {
    import WrappedService = SimpleEnumV2
    function method WrappedDefaultSimpleEnumV2Config(): SimpleEnumV2Config {
        SimpleEnumV2Config
    }
}
