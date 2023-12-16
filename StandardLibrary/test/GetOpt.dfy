// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/StandardLibrary.dfy"
include "../src/GetOpt.dfy"

module GetOptTest {
  import opened Wrappers
  import opened GetOpt


  method {:test} TestEmpty() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText"),
                               Param.Opt("bar", "helpText"),
                               Param.Opt("two", "helpText", short := 't'),
                               Param.Flag("six", "helpText", short := 's')
                             ]);
    var x :- expect GetOptions(MyOptions, ["cmd"]);
    expect x.params == [];
    expect x.files == [];
  }

  method {:test} TestShort() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText"),
                               Param.Opt("bar", "helpText"),
                               Param.Opt("two", "helpText", short := 't'),
                               Param.Flag("six", "helpText", short := 's'),
                               Param.Flag("seven", "helpText", short := 'v')
                             ]);
    var x :- expect GetOptions(MyOptions, ["cmd", "-svsttt", "-t", "stuff", "-v"]);
    expect x.params == [OneArg("six", None), OneArg("seven", None), OneArg("six", None), OneArg("two", Some("tt")),
                        OneArg("two", Some("stuff")), OneArg("seven", None)];
    expect x.files == [];
  }

  method {:test} TestLong() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText"),
                               Param.Opt("bar", "helpText"),
                               Param.Opt("two", "helpText", short := 't'),
                               Param.Flag("six", "helpText", short := 's'),
                               Param.Flag("seven", "helpText", short := 'v')
                             ]);
    var x :- expect GetOptions(MyOptions, ["cmd", "--foo", "file1", "--bar", "bar1", "-", "--bar=bar2=bar3", "file3", "--", "--this", "-that"]);
    expect x.params == [OneArg("foo", None), OneArg("bar", Some("bar1")), OneArg("bar", Some("bar2=bar3"))];
    expect x.files == ["file1", "-", "file3", "--this", "-that"];
  }

  method {:test} TestRequired() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText"),
                               Param.Opt("bar", "helpText", unused := Required),
                               Param.Opt("two", "helpText", short := 't'),
                               Param.Flag("six", "helpText", short := 's'),
                               Param.Flag("seven", "helpText", short := 'v')
                             ]);
    var x :- expect GetOptions(MyOptions, ["cmd", "--foo", "file1", "--bar", "bar1", "-", "--bar=bar2=bar3", "file3", "--", "--this", "-that"]);
    expect x.params == [OneArg("foo", None), OneArg("bar", Some("bar1")), OneArg("bar", Some("bar2=bar3"))];
    expect x.files == ["file1", "-", "file3", "--this", "-that"];

    var y := GetOptions(MyOptions, ["cmd", "--foo", "file1", "file3", "--", "--this", "-that"]);
    expect y.Failure?;
    expect y.error == "Option 'bar' is required, but was not used.";
  }

  method {:test} TestDeprecated() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText", vis := Deprecated),
                               Param.Opt("bar", "helpText", vis := Deprecated),
                               Param.Opt("two", "helpText", short := 't'),
                               Param.Flag("six", "helpText", short := 's', vis := Deprecated),
                               Param.Flag("seven", "helpText", short := 'v')
                             ]);
    var x :- expect GetOptions(MyOptions, ["cmd", "--foo", "--bar=baz", "-svtstuff"]);
    expect x.params == [OneArg("seven", None), OneArg("two", Some("stuff"))];
    expect x.files == [];
  }

  method {:test} TestAlias() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText", shortAlias := "abc", longAlias := ["def", "ghi"]),
                               Param.Opt("bar", "helpText", vis := Deprecated),
                               Param.Opt("two", "helpText", short := 't'),
                               Param.Flag("six", "helpText", short := 's', vis := Deprecated),
                               Param.Flag("seven", "helpText", short := 'v')
                             ]);
    var x :- expect GetOptions(MyOptions, ["cmd", "-abc", "--def", "--ghi"]);
    expect x.params == [OneArg("foo", None), OneArg("foo", None), OneArg("foo", None), OneArg("foo", None), OneArg("foo", None)];
    expect x.files == [];
  }

  method {:test} TestPositionalFail() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText"),
                               Param.Opt("two", "helpText", positional := Maybe),
                               Param.Opt("bar", "helpText", positional := Yes)
                             ]);
    var x := GetOptions(MyOptions, ["cmd", "stuff", "-123", "--foo"]);
    expect x.Failure?;
    expect x.error == "Required positional argument 'bar' follows optional positional argument 'two'.";
  }

  method {:test} TestPositional() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText"),
                               Param.Opt("bar", "helpText", positional := Yes),
                               Param.Opt("two", "helpText", positional := Maybe)
                             ]);
    var x :- expect GetOptions(MyOptions, ["cmd", "stuff", "-123", "--foo"]);
    expect x.params == [OneArg("bar", Some("stuff")), OneArg("two", Some("-123")), OneArg("foo", None)];
    expect x.files == [];

    x :- expect GetOptions(MyOptions, ["cmd", "stuff", "--two=-123", "--foo"]);
    expect x.params == [OneArg("bar", Some("stuff")), OneArg("two", Some("-123")), OneArg("foo", None)];
    expect x.files == [];

    x :- expect GetOptions(MyOptions, ["cmd", "stuff", "--two=-123", "--foo", "--bar", "more-stuff"]);
    expect x.params == [OneArg("bar", Some("stuff")), OneArg("two", Some("-123")), OneArg("foo", None), OneArg("bar", Some("more-stuff"))];
    expect x.files == [];

    x :- expect GetOptions(MyOptions, ["cmd", "stuff"]);
    expect x.params == [OneArg("bar", Some("stuff"))];
    expect x.files == [];

    var y := GetOptions(MyOptions, ["cmd", "--two=-123", "--foo", "--bar", "more-stuff"]);
    expect y.Failure?;
    expect y.error == "Positional arg bar matched with invalid positional value '--two=-123'.";

    y := GetOptions(MyOptions, ["cmd"]);
    expect y.Failure?;
    expect y.error == "Positional arg 'bar' is required, but we've run out of arguments.";
  }

  method {:test} TestHelp() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText"),
                               Param.Opt("bar", "helpText"),
                               Param.Opt("two", "helpText", short := 't'),
                               Param.Flag("six", "helpText", short := 's'),
                               Param.Flag("seven", "helpText", short := 'v')
                             ]);
    var x :- expect GetOptions(MyOptions, ["cmd", "--help"]);
    var y :- expect NeedsHelp(MyOptions, x);
    print "\n", y, "\n";
  }

  method {:test} TestHelpFail() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "helpText"),
                               Param.Opt("bar", "helpText"),
                               Param.Opt("two", "helpText", short := 't'),
                               Param.Flag("six", "helpText", short := 's'),
                               Param.Flag("seven", "helpText", short := 'v')
                             ]);
    var x := GetOptions(MyOptions, ["cmd", "--help", "--foo"]);
    expect x.Failure?;
    expect x.error == "Option 'help' used with other stuff, but must only be used alone.";
  }

  method {:test} TestNested() {
    var MyOptions := Options("MyProg", "does stuff",
                             [
                               Param.Flag("foo", "Does foo things"),
                               Param.Opt("two", "Does bar things to thingy", short := 't', argName := "thingy"),
                               Param.Command(Options("command", "Does command stuff", [
                                                       Param.Opt("five", "Does five things to thingy", short := 'h', argName := "thingy"),
                                                       Param.Flag("six", "Does six things", inherit := true)
                                                     ])),
                               Param.Command(Options("other", "Does other stuff", [
                                                       Param.Opt("seven", "Does seven things to thingy", short := 'h', argName := "thingy"),
                                                       Param.Flag("eight", "Does eight things")
                                                     ]))
                             ]);
    var x :- expect GetOptions(MyOptions, ["MyProg", "--foo", "other", "--seven=siete", "--eight"]);
    expect x.command == "MyProg";
    expect x.params == [OneArg("foo", None)];
    expect x.files == [];
    expect x.subcommand.Some?;
    var sub := x.subcommand.value;
    expect sub.command == "other";
    expect sub.params == [OneArg("seven", Some("siete")), OneArg("eight", None)];
    expect sub.files == [];
    expect sub.subcommand.None?;

    x :- expect GetOptions(MyOptions, ["MyProg", "--help"]);
    var y :- expect NeedsHelp(MyOptions, x);
    print "\n", y, "\n";

    x :- expect GetOptions(MyOptions, ["MyProg", "command", "--help"]);
    y :- expect NeedsHelp(MyOptions, x);
    print "\n", y, "\n";
  }

  method {:test} TestDefault() {
    var MyOptions := Options(
      "MyProg",
      "does stuff",
      [
        Param.Flag("foo", "Does foo things"),
        Param.Opt("two", "Does bar things to thingy", short := 't', argName := "thingy", unused := Default("two_dflt")),
        Param.Command(Options(
                        "command", "Does command stuff", [
                          Param.Opt("five", "Does five things to thingy", short := 'h', argName := "thingy", unused := Default("five_dflt")),
                          Param.Flag("six", "Does six things")
                        ]
                      )),
        Param.Command(Options(
                        "other", "Does other stuff", [
                          Param.Opt("seven", "Does seven things to thingy", short := 'h', argName := "thingy", unused := Default("seven_dflt")),
                          Param.Flag("eight", "Does eight things")
                        ]
                      ))
      ]
    );
    var x :- expect GetOptions(MyOptions, ["cmd", "--foo", "other", "--eight"]);
    expect x.command == "cmd";
    expect x.params == [OneArg("foo", None), OneArg("two", Some("two_dflt"))];
    expect x.files == [];
    expect x.subcommand.Some?;
    var sub := x.subcommand.value;
    expect sub.command == "other";
    expect sub.params == [OneArg("eight", None), OneArg("seven", Some("seven_dflt"))];
    expect sub.files == [];
    expect sub.subcommand.None?;

    x :- expect GetOptions(MyOptions, ["cmd", "--foo", "command", "--six"]);
    expect x.command == "cmd";
    expect x.params == [OneArg("foo", None), OneArg("two", Some("two_dflt"))];
    expect x.files == [];
    expect x.subcommand.Some?;
    sub := x.subcommand.value;
    expect sub.command == "command";
    expect sub.params == [OneArg("six", None), OneArg("five", Some("five_dflt"))];
    expect sub.files == [];
    expect sub.subcommand.None?;

    x :- expect GetOptions(MyOptions, ["cmd", "--foo"]);
    expect x.command == "cmd";
    expect x.params == [OneArg("foo", None), OneArg("two", Some("two_dflt"))];
    expect x.files == [];
    expect x.subcommand.None?;
  }

  method {:test} TestDdbec() {
    var MyOptions := Options(
      "ddbec", "Test the ddbec",
      [
        Param.Command(Options(
                        "encrypt", "Encrypts record",
                        [
                          Param.Opt("output", "Write encrypted records to fileName.", short := 'o', argName := "fileName")
                        ]
                      )),
        Param.Command(Options(
                        "decrypt", "Decrypts Records",
                        [
                          Param.Opt("expected", "fileName contains expected plaintext records.", short := 'e', argName := "fileName")
                        ]
                      ))
      ]
    );
  }
}
