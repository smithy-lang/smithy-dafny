include "../src/WrappedSimpleBlobImpl.dfy"
include "SimpleBlobImplTest.dfy"

module WrappedSimpleTypesBlobTest {
    import WrappedSimpleTypesBlobService
    import SimpleBlobImplTest
    import opened Wrappers
    method{:test} GetBlob() {
        var client :- expect WrappedSimpleTypesBlobService.WrappedSimpleBlob();
        SimpleBlobImplTest.TestGetBlob(client);
    }
}