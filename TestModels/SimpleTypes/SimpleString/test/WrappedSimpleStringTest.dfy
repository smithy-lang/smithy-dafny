include "../src/WrappedSimpleStringImpl.dfy"
include "SimpleStringImplTest.dfy"

module WrappedSimpleTypesStringTest {
    import WrappedSimpleTypesStringService
    import SimpleStringImplTest
    import opened Wrappers
    method{:test} GetString() {
        var client :- expect WrappedSimpleTypesStringService.WrappedSimpleString();
        SimpleStringImplTest.TestGetString(client);
        SimpleStringImplTest.TestGetStringSingleValue(client);
        SimpleStringImplTest. TestGetStringUTF8(client);
    }
}