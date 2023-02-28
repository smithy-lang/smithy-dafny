include "../src/WrappedSimpleExternImpl.dfy"
include "SimpleExternImplTest.dfy"

module WrappedSimpleExternTest {
    import WrappedSimpleExternService
    import opened SimpleExternTypes
    import SimpleExternImplTest
    import opened Wrappers
    
    method{:test} Externs() {
        var client :- expect WrappedSimpleExternService.WrappedSimpleExtern();
        SimpleExternImplTest.TestGetExtern(client);
        SimpleExternImplTest.TestExternMustError(client);
        SimpleExternImplTest.TestUseClassExternSuccess(client);
        SimpleExternImplTest.TestUseClassExternFailure(client);
    }
}