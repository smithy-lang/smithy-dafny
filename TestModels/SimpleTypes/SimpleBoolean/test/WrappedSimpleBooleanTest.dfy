include "../src/WrappedSimpleBooleanImpl.dfy"
include "SimpleBooleanImplTest.dfy"

module WrappedSimpleTypesBooleanTest {
    import WrappedSimpleTypesBooleanService
    import SimpleBooleanImplTest
    import opened Wrappers
    method{:test} GetBoolean() {
        var client :- expect WrappedSimpleTypesBooleanService.WrappedSimpleBoolean();
        SimpleBooleanImplTest.TestGetBoolean(client);
    }
}