include "../src/WrappedSimpleRefinementImpl.dfy"
include "SimpleRefinementImplTest.dfy"

module WrappedSimpleRefinementTest {
    import WrappedSimpleRefinementService
    import SimpleRefinementImplTest
    import opened Wrappers
    method{:test} Refinement() {
        var client :- expect WrappedSimpleRefinementService.WrappedSimpleRefinement();
        SimpleRefinementImplTest.TestGetRefinement(client);
        SimpleRefinementImplTest.TestOnlyInput(client);
        SimpleRefinementImplTest.TestOnlyOutput(client);
        SimpleRefinementImplTest.TestReadonlyOperation(client);

    }
}