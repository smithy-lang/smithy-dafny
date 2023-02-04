include "../src/WrappedSimpleErrorsImpl.dfy"
include "SimpleErrorsImplTest.dfy"

module WrappedSimpleErrorsTest {
    import WrappedSimpleErrorsService
    import SimpleErrorsImplTest
    import opened Wrappers
    method{:test} GetErrors() {
        var client :- expect WrappedSimpleErrorsService.WrappedSimpleErrors();
        SimpleErrorsImplTest.TestAlwaysError(client);
    }
}