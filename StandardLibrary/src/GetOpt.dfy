// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/*
Types :
    Options = (name : string, help : string, params : seq<Params>)
    datatype Param =
      Opt(name: string, argName: string, help: string, nameonly short : char) // takes an argument
      Flag(name: string, help: string, nameonly short : char) // does not take an argument
      Command(options: Options) // sub command
    Parsed = (command : string, params : seq<OneArg>, files : seq<string>, subcommand : Option<Parsed>)
    OneArg (name : string, value : Option<string>) // for Opt value.Some? for Flag value.None?

Main Entry Points :
  GetOptions(opts : Options, args : seq<string>) : Parsed // Parse args based on Options, automatically includes --help
  NeedsHelp(opts : Options, args : Parsed) : Option<string> // return help text, if --help was used

Helpers for `Opt` args :
  OptValue(args : seq<OneArg>, arg : string) : Option<string> // return value for arg, if used
  OptMapLast(args : seq<OneArg>) : map<string, string> // return args as map, return last value used if multiple
  OptMapList(args : seq<OneArg>) : map<string, seq<string>> // return all values for each arg used
  OptMapCheck(args : seq<OneArg>) : Result<map<string, string>, string> // as OptMapLast, but return error if any are used more than once

Helpers for `Flag` args :
  FlagCount(args : seq<OneArg>, arg : string) : nat // how many times was arg used
  FlagsSet(args : seq<OneArg>) : set<string> // set of all Flags used at least once
  FlagMapCount(args : seq<OneArg>) : map<string, nat> // // for each Flag used, how many times was it used
  FlagSetCheck(args : seq<OneArg>) : Result<set<string>, string> // as FlagSet, but return error if any are used more than once

Helper for argument values :
  None yet, but should parse numbers, enums, timestamps, dates, boolean, tristate, duration, and lists of all of these

Command Line Interpretations :
  We attempt to mostly match the GNU/POSIX standard, such as it is

  If "cmd" has
    Opt("Apple", Some('a'))
    Opt("Banana", Some('b'))
    Flag("Cherry", Some('c'))
    Flag("Date", Some('d'))
  then these are all equivalent
    cmd --cherry --apple red --banana yellow --date
    cmd --cherry --apple=red --banana=yellow --date
    cmd -c -a red -b yellow -d
    cmd -ca red -byellow -d
    cmd -cared -byellow -d
  and these are all equivalent
    cmd --cherry --apple red --banana yellow --date file1 file2 file3 file4 file5
    cmd file1 --cherry file2 --apple red file3 --banana yellow file4 --date file5
    cmd file1 -c file2 -a red file3 -b yellow file4 -d file5
  
  Everything after "--" is a file name, so
    cmd --cherry --date
  has two parameters and no files, while
    cmd --cherry -- --date
  has one parameter and one file (file name is "--date")

  If cmd has a subcommand, then it can take no file parameters
  e.g. if cmd has a subcommand sub then
    cmd --cherry sub --whatever file1
  is fine, but
    cmd --cherry file1 sub --whatever 
  returns the error "subcommand 'file1' not recognized"

Specialized Options for both Opt and Flag
  nameonly inherit : bool // all subcommands inherit this Param
  nameonly vis : Visibility // should this option be hidden from help or results
  nameonly shortAlias : seq<char> // these short option characters also point to this same option
  nameonly longAlias : seq<char> // these long option strings also point to this same option
  // aliases do not appear in help. returned arg name is the option's name, not the alias's

Specialized Options for Opt
  nameonly unused : Unused // if not used, raise an error or provide a default
  nameonly positional : Tri // positional parameters, required or optional
  // a positional MUST NOT start with a - unless it followed by exclusively digits

Specialized Options for Flag
  nameonly bool solo // if this flag is used, no other Options may be used

Future Directions (NOT ordered) :

  leading positional arguments, e.g. MyProg X Y Z --arg value --arg value
    Opt has
      nameonly positional : Tri := No
    order in list is order of positionals
    all Yes's must precede all Maybe's

  if X is used, Y is required
  if X is used, Y is not required
  if X is used, Y is forbidden
  if X is used, Y gets this default value
  exactly one of X, Y, Z is required (but better to have "--thing (X or Y or Z)" be required)

  value of --arg is everything to the right; presumably joined on space
  better formatting and word wrapping for help text

Not Future Directions :
  Automatic printing of --help text, and subsequent exit.
  Any attempt to automatically parse args into real values.
    (but we DO want to provide many helper functions for this)
  Arg with optional value
  Arg with multiple values
  case-insensitive argument matching
*/

include "../../libraries/src/Wrappers.dfy"
  //include "../../../../submodules/MaterialProviders/libraries/src/Collections/Sequences/Seq.dfy"

module {:options "-functionSyntax:4"} GetOpt {
  import opened Wrappers
    // import Seq, replace when repaired

  method Example(args : seq<string>) returns (output : Result<bool, string>)
    requires 0 < |args|
  {
    var MyOptions := [
      Param.Flag("foo", "Does foo things"),
      Param.Opt("two", "Does bar things to thingy", short := 't', argName := "thingy"),
      Param.Command(Options("command", "Does command stuff", [
                              Param.Opt("two", "Does bar things to thingy", short := 't', argName := "thingy"),
                              Param.Flag("foo", "Does foo things")
                            ]))
    ];

    var opts := Options("myProg", "does prog stuff", MyOptions);
    var x :- GetOptions(opts, args);
    var h := NeedsHelp(opts, x);
    if h.Some? {
      print h.value;
      return Success(true);
    }
    // deal with x.params
    // deal with x.files
    // deal with x.subcommand
    return Success(true);
  }

  /* Returns the subsequence consisting of those elements of a sequence that satisfy a given
    predicate. */
  function {:opaque} Filter<T>(f: (T ~> bool), xs: seq<T>): (result: seq<T>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures |result| <= |xs|
    ensures forall i: nat :: i < |result| && f.requires(result[i]) ==> f(result[i])
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
  {
    if |xs| == 0 then []
    else (if f(xs[0]) then [xs[0]] else []) + Filter(f, xs[1..])
  }

  datatype Tri = Yes | No | Maybe
  datatype Visibility = Normal | Hidden | Deprecated

  const NullChar : char := 0 as char

  datatype Options = Options (
    name : string,
    help : string,
    params : seq<Param>
  )

  datatype Unused = UnusedOk | Required | Default(val : string)

  datatype Param =
    | Opt(
        name: string,
        help: string,
        nameonly argName: string := "arg",
        nameonly short: char := NullChar,
        nameonly unused : Unused := UnusedOk,
        nameonly inherit : bool := false,
        nameonly vis : Visibility := Normal,
        nameonly shortAlias : seq<char> := [],
        nameonly longAlias : seq<string> := [],
        nameonly positional : Tri := No
      )
    | Flag(
        name: string,
        help: string,
        nameonly short: char := NullChar,
        nameonly solo : bool := false,
        nameonly inherit : bool := false,
        nameonly vis : Visibility := Normal,
        nameonly shortAlias : seq<char> := [],
        nameonly longAlias : seq<string> := []
      )
    | Command(
        options : Options
      )
  {
    predicate NeedsArg()
    {
      this.Opt?
    }
    predicate Inherits()
    {
      (this.Opt? || this.Flag?) && this.inherit
    }
    predicate ShowHelp()
    {
      this.Command? || this.vis == Normal
    }
    predicate KeepResult()
    {
      this.Command? || this.vis != Deprecated
    }
    function Name() : string
    {
      if this.Command? then
        options.name
      else
        name
    }
    function MakeArg(value : Option<string>) : seq<OneArg>
    {
      if this.KeepResult() then
        [OneArg(Name(), value)]
      else
        []
    }
    function ShortAlias() : seq<char>
    {
      if this.Command? then
        []
      else
        shortAlias
    }
    function LongAlias() : seq<string>
    {
      if this.Command? then
        []
      else
        longAlias
    }
    predicate Required()
    {
      this.Opt? && this.unused.Required?
    }
    predicate HasDefault()
    {
      this.Opt? && this.unused.Default?
    }
  }

  function {:tailrecursion} NeedsHelp(opts : Options, args : Parsed, prefix : string := "") : Option<string>
  {
    if |args.params| != 0 && args.params[0].name == HELP_STR then
      Some(GetHelp(opts, prefix))
    else if args.subcommand.Some? then
      var pos :- GetSubOptions(opts.params, args.subcommand.value.command);
      NeedsHelp(opts.params[pos].options, args.subcommand.value, prefix + args.command + " ")
    else
      None
  }

  const HELP_STR : string := "help"
  const HELP_PARAM : Param := Param.Flag(HELP_STR, "This help text.", solo := true, inherit := true)

  function GetHelp(opts : Options, prefix : string := "") : string
  {
    var newOpts := opts.params + [HELP_PARAM];
    var longLen := GetLongLen(newOpts, 6);
    var commandLen := GetCommandLen(newOpts);
    if commandLen == 0 then
      "USAGE : " + prefix + opts.name + " [args...]\n" +
      opts.help + "\n" +
      GetHelp2(newOpts, longLen)
    else
      "USAGE : " + opts.name + " [args...] command [args...]\n" +
      opts.help + "\n" +
      "\nAvailable Commands:\n" +
      GetCmdHelp(newOpts, commandLen) +
      "\nAvailable Options:\n" +
      GetHelp2(newOpts, longLen)
  }

  datatype OneArg = OneArg (
    name : string,
    value : Option<string>
  )

  datatype Parsed = Parsed (
    command : string,
    params : seq<OneArg>,
    files : seq<string>,
    subcommand : Option<Parsed>
  )

  // get value of first occurrence of option with required argument.
  // Cannot distinguish "no value" from "argument not used"
  function OptValue(args : seq<OneArg>, arg : string) : Option<string>
  {
    if |args| == 0 then
      None
    else if args[0].name == arg then
      args[0].value
    else
      OptValue(args[1..], arg)
  }

  // return the number of times this option was specified
  // only useful if the option takes an argument
  function {:tailrecursion} FlagCount(args : seq<OneArg>, arg : string) : nat
  {
    if |args| == 0 then
      0
    else if args[0].name == arg then
      1 + FlagCount(args[1..], arg)
    else
      FlagCount(args[1..], arg)
  }

  function {:tailrecursion} OptMapLast(args : seq<OneArg>, theMap : map<string, string> := map[]) : map<string, string>
  {
    if |args| == 0 then
      theMap
    else if args[0].value.Some? then
      OptMapLast(args[1..], theMap[args[0].name := args[0].value.value])
    else
      OptMapLast(args[1..], theMap)
  }

  function {:tailrecursion} FlagsSet(args : seq<OneArg>, theSet : set<string> := {}) : set<string>
  {
    if |args| == 0 then
      theSet
    else if args[0].value.Some? then
      FlagsSet(args[1..], theSet)
    else
      FlagsSet(args[1..], theSet + {args[0].name})
  }

  function {:tailrecursion} OptMapList(args : seq<OneArg>, theMap : map<string, seq<string>> := map[]) : (ret : map<string, seq<string>>)
    requires forall k <- theMap :: 0 < |theMap[k]|
    ensures forall k <- ret :: 0 < |ret[k]|
  {
    if |args| == 0 then
      theMap
    else if args[0].value.Some? then
      if args[0].name in theMap then
        OptMapList(args[1..], theMap[args[0].name := theMap[args[0].name] + [args[0].value.value]])
      else
        OptMapList(args[1..], theMap[args[0].name := [args[0].value.value]])
    else
      OptMapList(args[1..], theMap)
  }

  function {:tailrecursion} FlagMapCount(args : seq<OneArg>, theMap : map<string, nat> := map[]) : (ret : map<string, nat>)
    requires forall k <- theMap :: 0 < theMap[k]
    ensures forall k <- ret :: 0 < ret[k]
  {
    if |args| == 0 then
      theMap
    else if args[0].value.Some? then
      FlagMapCount(args[1..], theMap)
    else if args[0].name in theMap then
      FlagMapCount(args[1..], theMap[args[0].name := theMap[args[0].name] + 1])
    else
      FlagMapCount(args[1..], theMap[args[0].name := 1])
  }


  function {:tailrecursion} FlagSetCheck(args : seq<OneArg>, theSet : set<string> := {}) : Result<set<string>, string>
  {
    if |args| == 0 then
      Success(theSet)
    else if args[0].value.Some? then
      if args[0].name in theSet then
        Failure("Duplicate arg : " + args[0].name)
      else
        FlagSetCheck(args[1..], theSet + {args[0].name})
    else
      FlagSetCheck(args[1..], theSet)
  }

  function {:tailrecursion} OptMapCheck(args : seq<OneArg>, theMap : map<string, string> := map[]) : Result<map<string, string>, string>
  {
    if |args| == 0 then
      Success(theMap)
    else if args[0].value.Some? then
      if args[0].name in theMap then
        Failure("Duplicate arg : " + args[0].name)
      else
        OptMapCheck(args[1..], theMap[args[0].name := args[0].value.value])
    else
      OptMapCheck(args[1..], theMap)
  }

  type CommandMap = x : map<string, Options> | forall k <- x :: x[k].name == k

  function GetHelpHelp(opt : Param) : string
  {
    if opt.Command? then
      ""
    else if opt.Flag? then
      opt.help
    else
      opt.help +
      if opt.Required() then
        " (required)"
      else if opt.HasDefault() then
        " (default : " + opt.unused.val + ")"
      else
        ""
  }

  function OneHelp(opt : Param, longLen : nat) : string
  {
    if opt.Command? || !opt.ShowHelp() then
      ""
    else
      GetShortHelp(opt) + "  " + GetLongHelp(opt, longLen) + "  " + GetHelpHelp(opt) + "\n"
  }

  function GetCommandHelp(opt : Param, commandLen : nat) : string
    requires opt.Command?
  {
    var name :=
      if |opt.options.name| < commandLen then
        opt.options.name + seq(commandLen - |opt.options.name|, i => ' ')
      else
        opt.options.name;
    name + "  " + opt.options.help + "\n"
  }

  function GetShortHelp(opt : Param) : (output : string)
  {
    if opt.Opt? || opt.Flag? then
      if opt.short != NullChar then
        "-" + [opt.short]
      else
        "  "
    else
      ""
  }

  function GetLongHelp(opt : Param, longLen : nat) : string
  {
    if opt.Opt? || opt.Flag? then
      var tmp :=
        "--" + opt.name +
        if opt.Opt? then
          "=" + opt.argName
        else
          "";
      if |tmp| < longLen then
        tmp + seq(longLen - |tmp|, i => ' ')
      else
        tmp
    else
      ""
  }

  function GetHelp2(opts : seq<Param>, longLen : nat) : string
  {
    if |opts| == 0 then
      ""
    else
      var x := OneHelp(opts[0], longLen);
      x + GetHelp2(opts[1..], longLen)
  }

  function GetCmdHelp(opts : seq<Param>, commandLen : nat) : string
  {
    if |opts| == 0 then
      ""
    else
      var x :=
        if opts[0].Command? then
          GetCommandHelp(opts[0], commandLen)
        else
          "";
      x + GetCmdHelp(opts[1..], commandLen)
  }

  function GetLongLen(opts : seq<Param>, max : nat := 0) : nat
  {
    if |opts| == 0 then
      max
    else
      var x := |GetLongHelp(opts[0], 0)|;
      var newMax := if x > max then x else max;
      GetLongLen(opts[1..], newMax)
  }

  function GetCommandLen(opts : seq<Param>, max : nat := 0) : nat
  {
    if |opts| == 0 then
      max
    else
      var x := if opts[0].Command? then |opts[0].options.name| else 0;
      var newMax := if x > max then x else max;
      GetCommandLen(opts[1..], newMax)
  }

  function AddShortAlias(
    aliases : seq<char>,
    shortMap : map<char, string>,
    name : string,
    ghost origLongMap : map<string, Param>,
    ghost origAliases : seq<char> := aliases,
    ghost origShortMap : map<char, string> := shortMap
  ) : (ret : Result<map<char, string>, string>)
    requires name in origLongMap
    requires forall x <- shortMap :: shortMap[x] in origLongMap
    requires forall k <- origShortMap :: k in shortMap && shortMap[k] == origShortMap[k]
    requires forall k <- origAliases :: k in aliases || (k in shortMap && shortMap[k] == name)
    requires forall k <- shortMap ::
               || (k in origShortMap && shortMap[k] == origShortMap[k])
               || (shortMap[k] == name)
    ensures ret.Success? ==>
              && (forall k <- origShortMap :: k in ret.value && ret.value[k] == origShortMap[k])
              && (forall k <- origAliases :: k in ret.value && ret.value[k] == name)
              && (forall x <- ret.value :: ret.value[x] in origLongMap)
  {
    if |aliases| == 0 then
      Success(shortMap)
    else if aliases[0] in shortMap then
      Failure("Short alias '" + aliases[0..1] + "' for '" + name + "' already in use as a short option.")
    else
      AddShortAlias(aliases[1..], shortMap[aliases[0] := name], name, origLongMap, origAliases, origShortMap)
  }

  function AddLongAlias(
    aliases : seq<string>,
    longMap : map<string, Param>,
    opt : Param
  ) : (ret : Result<map<string, Param>, string>)
    ensures ret.Success? ==>
              forall k <- longMap :: k in ret.value
  {
    if |aliases| == 0 then
      Success(longMap)
    else if aliases[0] in longMap then
      Failure("Long alias '" + aliases[0] + "' already in use as a long option.")
    else
      AddLongAlias(aliases[1..], longMap[aliases[0] := opt], opt)
  }

  // convert opts to the various maps that make parsing possible
  function {:tailrecursion} GetMaps(
    opts : seq<Param>,
    longMap : map<string, Param> := map[],
    shortMap : map<char, string> := map[],
    commandMap : CommandMap := map[])
    : (ret : Result<(map<string, Param>, map<char, string>, CommandMap), string>)
    requires forall x <- shortMap :: shortMap[x] in longMap
    ensures ret.Success? ==> (forall x <- ret.value.1 :: ret.value.1[x] in ret.value.0)
  {
    if |opts| == 0 then
      Success((longMap, shortMap, commandMap))
    else
      var opt := opts[0];
      if opt.Command? then
        :- Need(opt.options.name !in commandMap, "Duplicate command in options : " + opt.options.name);
        GetMaps(opts[1..], longMap, shortMap, commandMap[opt.options.name := opt.options])
      else
        :- Need(opt.name !in longMap, "Duplicate long name in options : " + opt.name);
        var longMap := longMap[opt.name := opt];
        var shortMap :- AddShortAlias(opt.ShortAlias(), shortMap, opt.name, longMap);
        var longMap :- AddLongAlias(opt.LongAlias(), longMap, opt);
        if opt.short != NullChar then
          var short := opt.short;
          if short in shortMap then // can't be a `Need` because shortMap[short] required in message
            Failure("Duplicate short char in options : '" + [short] + "' for " + opt.name + " and " + shortMap[short])
          else
            GetMaps(opts[1..], longMap[opt.name := opt], shortMap[short := opt.name], commandMap)
        else
          GetMaps(opts[1..], longMap[opt.name := opt], shortMap, commandMap)
  }

  function Print<T>(x: T): Outcome<string> {
    Pass
  } by method {
    print x,"\n";
    return Pass;
  }

  predicate {:tailrecursion} ArgExists(args : seq<OneArg>, name : string)
  {
    if |args| == 0 then
      false
    else if args[0].name == name then
      true
    else
      ArgExists(args[1..], name)
  }

  function {:tailrecursion} PostProcess2(opts : seq<Param>, args : seq<OneArg>, newArgs : seq<OneArg> := []) : Result<seq<OneArg>, string>
  {
    if |opts| == 0 then
      Success(newArgs)
    else if opts[0].Opt? && opts[0].Required() && !ArgExists(args, opts[0].name) then
      Failure("Option '" + opts[0].name + "' is required, but was not used.")
    else if opts[0].Opt? && opts[0].HasDefault() && !ArgExists(args, opts[0].name) then
      PostProcess2(opts[1..], args, newArgs + [OneArg(opts[0].name, Some(opts[0].unused.val))])
    else
      PostProcess2(opts[1..], args, newArgs)
  }

  // return position of option which is the subcommand of this name
  function {:tailrecursion} GetSubOptions(opts : seq<Param>, name : string, pos : nat := 0) : (ret : Option<nat>)
    requires pos <= |opts|
    ensures ret.Some? ==> 0 < |opts| && ret.value < |opts| && opts[ret.value].Command? && opts[ret.value].options.name == name
    decreases |opts|-pos
  {
    if |opts| == pos then
      None
    else if opts[pos].Command? && opts[pos].options.name == name then
      Some(pos)
    else
      GetSubOptions(opts, name, pos+1)
  }

  function /*{:tailrecursion}*/ PostProcess(opts : Options, args : Parsed) : Result<Parsed, string>
  {
    var newParams :- PostProcess2(opts.params, args.params);
    if args.subcommand.Some? then
      var optPos := GetSubOptions(opts.params, args.subcommand.value.command);
      if optPos.Some? then
        var sub :- PostProcess(opts.params[optPos.value].options, args.subcommand.value);
        Success(args.(params := args.params + newParams, subcommand := Some(sub)))
      else
        Failure("Internal error in GetOpt::PostProcess")
    else
      Success(args.(params := args.params + newParams))
  }

  predicate AllDigits(s : string)
  {
    if |s| == 0 then
      true
    else if '0' <= s[0] <= '9' then
      AllDigits(s[1..])
    else
      false
  }
  predicate ValidPositional(s : string)
  {
    if |s| == 0 then
      true
    else if s[0] != '-' then
      true
    else
      AllDigits(s[1..])
  }

  function TestPositionals(opts : seq<Param>, optional : Option<string> := None) : Outcome<string>
  {
    if |opts| == 0 then
      Pass
    else if !opts[0].Opt? then
      TestPositionals(opts[1..], optional)
    else if opts[0].positional == No then
      TestPositionals(opts[1..], optional)
    else if opts[0].positional == Maybe then
      TestPositionals(opts[1..], Some(opts[0].name))
    else if optional.None? then
      TestPositionals(opts[1..], optional)
    else
      Fail("Required positional argument '" + opts[0].name + "' follows optional positional argument '" + optional.value + "'.")
  }

  function GetPositionals(opts : seq<Param>, args : seq<string>, params : seq<OneArg> := [])
    : (ret : Result<(seq<string>, seq<OneArg>), string>)
    ensures ret.Success? ==> |ret.value.0| <= |args|
  {
    if |opts| == 0 then
      Success((args, params))
    else if !opts[0].Opt? then
      GetPositionals(opts[1..], args, params)
    else if opts[0].positional == No then
      GetPositionals(opts[1..], args, params)
    else if opts[0].positional == Yes then
      if |args| == 0 then
        Failure("Positional arg '" + opts[0].name + "' is required, but we've run out of arguments.")
      else if ValidPositional(args[0]) then
        GetPositionals(opts[1..], args[1..], params + [OneArg(opts[0].name, Some(args[0]))])
      else
        Failure("Positional arg " + opts[0].name + " matched with invalid positional value '" + args[0] + "'.")
    else
      assert opts[0].positional == Maybe;
      if |args| == 0 then
        Success((args, params))
      else if ValidPositional(args[0]) then
        GetPositionals(opts[1..], args[1..], params + [OneArg(opts[0].name, Some(args[0]))])
      else
        Success((args, params))
  }

  function GetOptions(opts : Options, args : seq<string>) : Result<Parsed, string>
    requires 0 < |args|
    decreases args
  {
    var newOpts := opts.params + [HELP_PARAM];
    var inherits := Filter((o : Param) => o.Inherits(), newOpts);
    :- TestPositionals(newOpts);
    var (newArgs, params) :- GetPositionals(newOpts, args[1..]);
    var (longMap, shortMap, commandMap) :- GetMaps(newOpts);
    var context := Context(longMap, shortMap, inherits, commandMap, args[0]);
    var result :- GetOptions2(newArgs, context, params);
    PostProcess(opts, result)
  }

  datatype Context = Context (
    longMap : map<string, Param>,
    shortMap : map<char, string>,
    inherits : seq<Param>,
    commands : CommandMap,
    command : string
  )

  /* For an element that occurs at least once in a sequence, the index of its
     first occurrence is returned. */
  function {:opaque} IndexOf<T(==)>(xs: seq<T>, v: T): (i: nat)
    requires v in xs
    ensures i < |xs| && xs[i] == v
    ensures forall j :: 0 <= j < i ==> xs[j] != v
  {
    if xs[0] == v then 0 else 1 + IndexOf(xs[1..], v)
  }

  // split on first occurrence of delim, which must exist
  function SplitOnce<T(==)>(s: seq<T>, delim: T): (res : (seq<T>,seq<T>))
    requires delim in s
    ensures res.0 + [delim] + res.1 == s
    ensures !(delim in res.0)
  {
    var i := IndexOf(s, delim);
    (s[..i], s[(i + 1)..])
  }

  function /*{:tailrecursion}*/ GetOptions2(
    args : seq<string>,
    context : Context,
    parms : seq<OneArg> := [],
    files : seq<string> := [])
    : Result<Parsed, string>
    requires forall x <- context.shortMap :: context.shortMap[x] in context.longMap
    decreases args
  {
    if |args| == 0 then
      Success(Parsed(context.command, parms, files, None))
    else if args[0] in context.commands then
      var inherits := Filter((o : Param) => o.Inherits(), context.commands[args[0]].params);
      var newOpts := context.commands[args[0]].params + context.inherits;
      :- TestPositionals(newOpts);
      var (newArgs, params) :- GetPositionals(newOpts, args[1..]);
      var (longMap, shortMap, commandSet) :- GetMaps(newOpts);
      var newContext := Context(longMap, shortMap, context.inherits + inherits, commandSet, args[0]);
      var lostArgs := |args| - |newArgs|;
      var result :- GetOptions2(args[lostArgs..], newContext, params); // this is why it can't be tail recursive
      Success(Parsed(context.command, parms, files, Some(result)))
    else if args[0] == "--" then
      Success(Parsed(context.command, parms, files + args[1..], None))
    else if "--" < args[0] then
      var longOpt := args[0][2..];
      if '=' in longOpt then
        var (opt,arg) := SplitOnce(longOpt, '=');
        if opt in context.longMap then
          if context.longMap[opt].NeedsArg() then
            GetOptions2(args[1..], context, parms + context.longMap[opt].MakeArg(Some(arg)), files)
          else
            Failure("Option " + opt + " does not take an argument, but it got one.")
        else
          Failure("Option " + opt + " not recognized.")
      else
      if longOpt in context.longMap then
        var opt := context.longMap[longOpt];
        if opt.NeedsArg() then
          if |args| < 2 then
            Failure("Option " + longOpt + " requires an argument, but didn't get one.")
          else
            GetOptions2(args[2..], context, parms + opt.MakeArg(Some(args[1])), files)
        else if opt.Flag? && opt.solo && (|args| != 1 || |parms| != 0 || |files| != 0) then
          Failure("Option '" + longOpt + "' used with other stuff, but must only be used alone.")
        else
          GetOptions2(args[1..], context, parms + opt.MakeArg(None), files)
      else
        Failure("Option " + longOpt + " not recognized.")
    else if "-" == args[0] then
      GetOptions2(args[1..], context, parms, files + [args[0]])
    else if "-" < args[0] then
      var (newParms, nextParm) :- GetShort(args[0][1..], context.longMap, context.shortMap);
      if nextParm.None? then
        GetOptions2(args[1..], context, parms + newParms, files)
      else if |args| == 1 then
        Failure("Short option " + [nextParm.value] + " requires argument but didn't get one.")
      else
        var longOpt := context.shortMap[nextParm.value];
        var opt := context.longMap[longOpt];
        GetOptions2(args[2..], context, parms + newParms + opt.MakeArg(Some(args[1])), files)
    else if |context.commands| == 0 then
      GetOptions2(args[1..], context, parms, files + [args[0]])
    else
      Failure("Unrecognized command " + args[0] + " for " + context.command + "\nRun '" + context.command + " --help' for usage.")
  }

  function GetShort(arg : string, longMap : map<string, Param>, shortMap : map<char, string>, parms : seq<OneArg> := [])
    : (res : Result<(seq<OneArg>, Option<char>), string>)
    requires forall x <- shortMap :: shortMap[x] in longMap
    ensures res.Success? && res.value.1.Some? ==> res.value.1.value in shortMap
  {
    if |arg| == 0 then
      Success((parms, None))
    else
      var ch := arg[0];
      if ch in shortMap then
        var opt := shortMap[ch];
        if longMap[opt].NeedsArg() then
          if |arg| == 1 then
            Success((parms, Some(ch)))
          else
            Success((parms + longMap[opt].MakeArg(Some(arg[1..])), None))
        else
          GetShort(arg[1..], longMap, shortMap, parms + longMap[opt].MakeArg(None))
      else
        Failure("Short option '" + [ch] + "' not recognized.")
  }


}
