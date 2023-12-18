include "../src/IndexNet.dfy"

module NetSimpleExternV2ImplTest replaces SimpleExternV2ImplTest {
    import NetSimpleExternV2

    method{:test} NetExternV2Tests() {
        var ret := NetSimpleExternV2.CallOnlyNetExternMethod("only net!");
        expect ret == "only net!";
    }
}