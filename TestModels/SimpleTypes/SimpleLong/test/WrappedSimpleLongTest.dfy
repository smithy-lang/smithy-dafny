include "../src/WrappedSimpleLongImpl.dfy"
include "SimpleLongImplTest.dfy"

module WrappedSimpleTypesLongTest {
    import WrappedSimpleTypesLongService
    import SimpleLongImplTest
    import opened Wrappers
    method{:test} GetLong() {
        var client :- expect WrappedSimpleTypesLongService.WrappedSimpleLong();
        SimpleLongImplTest.TestGetLong(client);
        SimpleLongImplTest.TestGetLongEdgeCases(client);
        SimpleLongImplTest.TestGetLongKnownValueTest(client);
    }
}