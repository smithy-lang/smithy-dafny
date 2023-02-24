include "../src/WrappedSimpleUnionImpl.dfy"
include "SimpleUnionImplTest.dfy"

module WrappedSimpleUnionTest {
    import WrappedSimpleUnionService
    import SimpleUnionImplTest
    import opened Wrappers
    method{:test} TestUnion() {
        var client :- expect WrappedSimpleUnionService.WrappedSimpleUnion();
        SimpleUnionImplTest.TestMyUnionInteger(client);
        SimpleUnionImplTest.TestMyUnionString(client);

    }
}