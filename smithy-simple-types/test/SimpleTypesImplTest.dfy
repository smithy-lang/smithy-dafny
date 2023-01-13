include "../src/Index.dfy"

module  SimpleTypesImplTest {
    import SimpleTypes
    import opened Wrappers
    method{:test} GetString(){
        var client :- expect SimpleTypes.SimpleTypes();
        var ret := client.GetString(SimpleTypes.Types.GetStringInput(stringValue:= Some("S")));
        expect ret.Failure?;
        print ret;
    }
}
