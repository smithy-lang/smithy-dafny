include "../src/WrappedSimpleExternImpl.dfy"
include "SimpleExternImplTest.dfy"

module WrappedSimpleExternTest {
    import WrappedSimpleExternService
    import opened SimpleExternTypes
    import SimpleExternImplTest
    import opened Wrappers
    
    method{:test} Extern() {
        var client :- expect WrappedSimpleExternService.WrappedSimpleExtern();
        SimpleExternImplTest.TestGetExtern(client);
    }
}