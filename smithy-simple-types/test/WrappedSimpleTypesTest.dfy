include "WrappedSimpleTypesImpl.dfy"

module WrappedSimpletypesServiceTest {
    import WrappedSimpletypesService
    import SimpleTypes
    import opened Wrappers
    method{:test} GetString() {
        var client :- expect WrappedSimpletypesService.WrappedSimpleTypes();
        var ret := client.GetString(SimpleTypes.Types.GetStringInput(stringValue:= Some("S")));
        expect ret.Success?;
        print ret;
    }
}