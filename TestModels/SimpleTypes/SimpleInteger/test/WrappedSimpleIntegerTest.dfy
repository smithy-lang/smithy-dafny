include "../src/WrappedSimpleIntegerImpl.dfy"
include "SimpleIntegerImplTest.dfy"

module WrappedSimpleTypesIntegerTest {
    import WrappedSimpleTypesIntegerService
    import SimpleIntegerImplTest
    import opened Wrappers
    method{:test} GetInteger() {
        var client :- expect WrappedSimpleTypesIntegerService.WrappedSimpleInteger();
        SimpleIntegerImplTest.TestGetInteger(client);
        SimpleIntegerImplTest.TestGetIntegerKnownValue(client);
    }
}