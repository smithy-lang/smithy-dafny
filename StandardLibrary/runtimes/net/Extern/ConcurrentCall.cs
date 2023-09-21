// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using System.Numerics;
using Microsoft.VisualBasic;
using Wrappers_Compile;
using ibyteseq = Dafny.ISequence<byte>;
using byteseq = Dafny.Sequence<byte>;
using icharseq = Dafny.ISequence<char>;
using charseq = Dafny.Sequence<char>;

namespace ConcurrentCall
{

    public partial class __default
    {
        public static void ConcurrentCall(ConcurrentCall.Callee callee, uint serialIters, uint concurrentIters)
        {
            Thread[] threadsArray = new Thread[concurrentIters];
            for (uint i = 0; i < concurrentIters; i++)
            {
                uint localNum = i;
                threadsArray[i] = new Thread(() =>
                {
                    for (uint j = 0; j < serialIters; ++j)
                    {
                        (callee).call(j, localNum);
                    };
                });
            }
            for (uint i = 0; i < concurrentIters; i++)
                threadsArray[i].Start();

            for (uint i = 0; i < concurrentIters; i++)
                threadsArray[i].Join();

        }
    }
}
