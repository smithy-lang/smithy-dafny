include "../src/WrappedSimpleEnumImpl.dfy"
include "SimpleEnumImplTest.dfy"

module WrappedSimpleTypesEnumTest {
    import WrappedSimpleTypesEnumV2Service
    import SimpleEnumV2ImplTest
    import opened Wrappers
    method{:test} GetEnum() {
        var client :- expect WrappedSimpleTypesEnumV2Service.WrappedSimpleEnumV2();
        SimpleEnumV2ImplTest.TestGetEnum(client);
        SimpleEnumV2ImplTest.TestGetEnumFirstKnownValueTest(client);
        SimpleEnumV2ImplTest.TestGetEnumSecondKnownValueTest(client);
        SimpleEnumV2ImplTest.TestGetEnumThirdKnownValueTest(client);
    }
}
