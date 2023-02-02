include "../src/WrappedSimpleEnumImpl.dfy"
include "SimpleEnumImplTest.dfy"

module WrappedSimpleTypesEnumTest {
    import WrappedSimpleTypesEnumService
    import SimpleEnumImplTest
    import opened Wrappers
    method{:test} GetEnum() {
        var client :- expect WrappedSimpleTypesEnumService.WrappedSimpleEnum();
        SimpleEnumImplTest.TestGetEnum(client);
    }
}