// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"
include "MplManifestOptions.dfy"
include "TestManifests.dfy"
include "CompleteVectors.dfy"

module {:options "-functionSyntax:4"} WrappedMaterialProvidersMain {
  import opened Wrappers
  import MplManifestOptions
  import Seq
  import CompleteVectors
  import TestManifests

  method Main(args: seq<string>) {
    // The expectation is that the first argument
    // is the filename or runtime
    expect 0 < |args|;
    var op? := ParseCommandLineOptions(args[1..]);

    if op?.Success? {
      // Do the work
      var op := op?.value;
      if
      case op.Decrypt? =>
      // var _ :- expect EsdkTestManifests.StartDecryptVectors(op);
      case op.Encrypt? =>
        var result := TestManifests.StartEncrypt(op);
        if result.Failure? {
          print result.error;
        }
        expect result.Success?;
      case op.EncryptManifest? =>
        var result := CompleteVectors.WriteStuff(op);
        if result.Failure? {
          print result.error;
        }
        expect result.Success?;
    } else {
      print op?.error;
      print "help";
    }
  }

  function ParseCommandLineOptions(args: seq<string>)
    : (output: Result<MplManifestOptions.ManifestOptions, string>)
  {
    :- Need(1 < |args|, "Not enough arguments.");
    :- Need(CommandOption?(args[0]), "Unknown argument:" + args[0]);

    var op
      := if (|args| - 1) % 2 == 0 then
           Options2Map(args[1..])
         else
           Options2Map(args[1..|args| - 1]);

    match args[0]
    case "decrypt" => ParseDecryptOptions(op)
    case "encrypt" => ParseEncryptOptions(op)
    case "encrypt-manifest" => ParseEncryptManifestOptions(op)
  }

  function ParseDecryptOptions(op: map<string, string>)
    : (output: Result<MplManifestOptions.ManifestOptions, string>)
    ensures output.Success? ==> output.value.Decrypt?
  {
    :- Need(DecryptOptions?(op), "Incorrect arguments");

    Success(MplManifestOptions.Decrypt(
              manifestPath := if Seq.Last(op["-manifest-path"]) == '/' then op["-manifest-path"] else op["-manifest-path"] + "/",
              testName := if "-test-name" in op then Some(op["-test-name"]) else None
            ))
  }

  function ParseEncryptOptions(op: map<string, string>)
    : (output: Result<MplManifestOptions.ManifestOptions, string>)
    ensures output.Success? ==> output.value.Encrypt?
  {
    :- Need(EncryptOptions?(op), "Incorrect arguments");

    Success(MplManifestOptions.Encrypt(
              manifestPath := if Seq.Last(op["-manifest-path"]) == '/' then op["-manifest-path"] else op["-manifest-path"] + "/",
              decryptManifestOutput := op["-decrypt-manifest-output"],
              testName := if "-test-name" in op then Some(op["-test-name"]) else None
            ))
  }

  function ParseEncryptManifestOptions(op: map<string, string>)
    : (output: Result<MplManifestOptions.ManifestOptions, string>)
    ensures output.Success? ==> output.value.EncryptManifest?
  {
    :- Need(EncryptManifestOptions?(op), "Incorrect arguments");

    Success(MplManifestOptions.EncryptManifest(
              encryptManifestOutput := if Seq.Last(op["-encrypt-manifest-output"]) == '/' then op["-encrypt-manifest-output"] else op["-encrypt-manifest-output"] + "/"
            ))
  }

  predicate CommandOption?(s: string)
  {
    || s == "decrypt"
    || s == "encrypt"
    || s == "encrypt-manifest"
  }

  predicate DecryptOptions?(op: map<string, string>)
  {
    && 1 <= |op| <= 2
    && "-manifest-path" in op
    && 0 < |op["-manifest-path"]|
    && (|op| == 2 ==> "-test-name" in op)
  }

  predicate EncryptOptions?(op: map<string, string>)
  {
    && 3 <= |op| <= 4
    && "-manifest-path" in op
    && 0 < |op["-manifest-path"]|
    && "-decrypt-manifest-output" in op
    && (|op| == 4 ==> "-test-name" in op)
  }

  predicate EncryptManifestOptions?(op: map<string, string>)
  {
    && 1 <= |op| <= 2
    && "-encrypt-manifest-output" in op
    && 0 < |op["-encrypt-manifest-output"]|
  }

  predicate DecryptSingleOptions?(op: map<string, string>)
  {
    && 3 == |op|
    && "-keys-path" in op
    && "-key-description" in op
    && "-base64-bytes" in op
  }

  predicate DecryptRequiredOptions?(s: string)
  {
    || s == "manifest-path"
  }

  function Options2Map(args: seq<string>)
    : (map<string, string>)
    requires |args| % 2 == 0
  {
    if |args| == 0 then
      map[]
    else
      var key, value := args[0], args[1];
      map[key := value] + Options2Map(args[2..])
  }

}
