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
    }

    method TestGetTimestamp(client: ISimpleTypesTimestampClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var dafnyTimestamp := "2024-06-11T12:34:56Z";
        var ret :- expect client.GetTimestamp(SimpleTimestamp.Types.GetTimestampInput(value:= Some(dafnyTimestamp)));
        expect ret.value == Some(dafnyTimestamp);
        print ret;
    }
}
