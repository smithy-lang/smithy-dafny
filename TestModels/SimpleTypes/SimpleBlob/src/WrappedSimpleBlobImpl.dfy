include "../Model/SimpleTypesBlobTypesWrapped.dfy"

module {:extern "simple.types.blob.internaldafny.wrapped"} WrappedSimpleTypesBlobService refines WrappedAbstractSimpleTypesBlobService {
    import WrappedService = SimpleBlob
    function method WrappedDefaultSimpleBlobConfig(): SimpleBlobConfig {
        SimpleBlobConfig
    }
}
