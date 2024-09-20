// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleTimestampImplTest {

    import SimpleTimestamp
    import opened SimpleTypesTimestampTypes
    import opened Wrappers

    method {:test} TestClient(){
        var client :- expect SimpleTimestamp.SimpleTimestamp();

        TestGetTimestamp(client);
        TestGetTimestampNoMs(client);
    }

    method TestGetTimestamp(client: ISimpleTypesTimestampClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var dafnyTimestamp := "2024-06-11T12:34:56.789Z";
        var ret :- expect client.GetTimestamp(SimpleTimestamp.Types.GetTimestampInput(value := Some(dafnyTimestamp)));
        expect ret.value == Some(dafnyTimestamp);
        print ret;
    }

    method TestGetTimestampNoMs(client: ISimpleTypesTimestampClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var dafnyTimestamp := "2024-06-11T12:34:56Z";
        var ret :- expect client.GetTimestamp(SimpleTimestamp.Types.GetTimestampInput(value := Some(dafnyTimestamp)));
        expect ret.value.Some?;
        var retTimestamp := ret.value.value;

        // It's okay if milliseconds are serialized, so only check for prefix
        expect |retTimestamp| > 0;
        expect retTimestamp[|retTimestamp| - 1] == 'Z';
        expect dafnyTimestamp[|dafnyTimestamp| - 1] <= retTimestamp[|retTimestamp| - 1];
        print ret;
    }
}
