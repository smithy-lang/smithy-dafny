include "../src/WrappedSimpleConstraintsImpl.dfy"
include "SimpleConstraintsImplTest.dfy"

module WrappedSimpleConstraintsTest {
    import WrappedSimpleConstraintsService
    import SimpleConstraintsImplTest
    import opened Wrappers
    method{:test} GetConstraints() {
        var client :- expect WrappedSimpleConstraintsService.WrappedSimpleConstraints();
        SimpleConstraintsImplTest.TestGetConstraintWithValidInputs(client);
    }
}