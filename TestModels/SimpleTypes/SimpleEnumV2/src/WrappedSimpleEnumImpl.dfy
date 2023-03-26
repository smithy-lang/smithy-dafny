include "../Model/SimpleTypesEnumV2TypesWrapped.dfy"

module {:extern "Dafny.Simple.Types.EnumV2.Wrapped"} WrappedSimpleTypesEnumV2Service refines WrappedAbstractSimpleTypesEnumV2Service {
    import WrappedService = SimpleEnumV2
    function method WrappedDefaultSimpleEnumV2Config(): SimpleEnumV2Config {
        SimpleEnumV2Config
    }
}
