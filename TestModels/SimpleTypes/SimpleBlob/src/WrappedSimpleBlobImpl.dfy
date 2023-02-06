include "../Model/SimpleTypesBlobTypesWrapped.dfy"

module {:extern "Dafny.Simple.Types.Blob.Wrapped"} WrappedSimpleTypesBlobService refines WrappedAbstractSimpleTypesBlobService {
    import WrappedService = SimpleBlob
    function method WrappedDefaultSimpleBlobConfig(): SimpleBlobConfig {
        SimpleBlobConfig
    }
}