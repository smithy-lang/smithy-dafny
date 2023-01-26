// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System.Linq; using System; namespace Simple.Aggregate.Wrapped {
 public static class TypeConversion {
 internal static Simple.Aggregate.GetAggregateInput FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput (Dafny.Simple.Aggregate.Types._IGetAggregateInput value) {
 Dafny.Simple.Aggregate.Types.GetAggregateInput concrete = (Dafny.Simple.Aggregate.Types.GetAggregateInput)value; Simple.Aggregate.GetAggregateInput converted = new Simple.Aggregate.GetAggregateInput(); if (concrete._simpleStringList.is_Some) converted.SimpleStringList = (System.Collections.Generic.List<string>) FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M16_simpleStringList(concrete._simpleStringList);
 if (concrete._structureList.is_Some) converted.StructureList = (System.Collections.Generic.List<Simple.Aggregate.StructureListElement>) FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M13_structureList(concrete._structureList);
 if (concrete._SimpleStringMap.is_Some) converted.SimpleStringMap = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M15_SimpleStringMap(concrete._SimpleStringMap);
 if (concrete._SimpleIntegerMap.is_Some) converted.SimpleIntegerMap = (System.Collections.Generic.Dictionary<string, int>) FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M16_SimpleIntegerMap(concrete._SimpleIntegerMap);
 if (concrete._very.is_Some) converted.Very = (Simple.Aggregate.Deeply) FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M4_very(concrete._very); return converted;
}
 internal static Dafny.Simple.Aggregate.Types._IGetAggregateInput ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput (Simple.Aggregate.GetAggregateInput value) {
 System.Collections.Generic.List<string> var_simpleStringList = value.IsSetSimpleStringList() ? value.SimpleStringList : (System.Collections.Generic.List<string>) null;
 System.Collections.Generic.List<Simple.Aggregate.StructureListElement> var_structureList = value.IsSetStructureList() ? value.StructureList : (System.Collections.Generic.List<Simple.Aggregate.StructureListElement>) null;
 System.Collections.Generic.Dictionary<string, string> var_simpleStringMap = value.IsSetSimpleStringMap() ? value.SimpleStringMap : (System.Collections.Generic.Dictionary<string, string>) null;
 System.Collections.Generic.Dictionary<string, int> var_simpleIntegerMap = value.IsSetSimpleIntegerMap() ? value.SimpleIntegerMap : (System.Collections.Generic.Dictionary<string, int>) null;
 Simple.Aggregate.Deeply var_very = value.IsSetVery() ? value.Very : (Simple.Aggregate.Deeply) null;
 return new Dafny.Simple.Aggregate.Types.GetAggregateInput ( ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M16_simpleStringList(var_simpleStringList) , ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M13_structureList(var_structureList) , ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M15_SimpleStringMap(var_simpleStringMap) , ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M16_SimpleIntegerMap(var_simpleIntegerMap) , ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M4_very(var_very) ) ;
}
 internal static Simple.Aggregate.GetAggregateOutput FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput (Dafny.Simple.Aggregate.Types._IGetAggregateOutput value) {
 Dafny.Simple.Aggregate.Types.GetAggregateOutput concrete = (Dafny.Simple.Aggregate.Types.GetAggregateOutput)value; Simple.Aggregate.GetAggregateOutput converted = new Simple.Aggregate.GetAggregateOutput(); if (concrete._simpleStringList.is_Some) converted.SimpleStringList = (System.Collections.Generic.List<string>) FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M16_simpleStringList(concrete._simpleStringList);
 if (concrete._structureList.is_Some) converted.StructureList = (System.Collections.Generic.List<Simple.Aggregate.StructureListElement>) FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M13_structureList(concrete._structureList);
 if (concrete._SimpleStringMap.is_Some) converted.SimpleStringMap = (System.Collections.Generic.Dictionary<string, string>) FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M15_SimpleStringMap(concrete._SimpleStringMap);
 if (concrete._SimpleIntegerMap.is_Some) converted.SimpleIntegerMap = (System.Collections.Generic.Dictionary<string, int>) FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M16_SimpleIntegerMap(concrete._SimpleIntegerMap);
 if (concrete._very.is_Some) converted.Very = (Simple.Aggregate.Deeply) FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M4_very(concrete._very); return converted;
}
 internal static Dafny.Simple.Aggregate.Types._IGetAggregateOutput ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput (Simple.Aggregate.GetAggregateOutput value) {
 System.Collections.Generic.List<string> var_simpleStringList = value.IsSetSimpleStringList() ? value.SimpleStringList : (System.Collections.Generic.List<string>) null;
 System.Collections.Generic.List<Simple.Aggregate.StructureListElement> var_structureList = value.IsSetStructureList() ? value.StructureList : (System.Collections.Generic.List<Simple.Aggregate.StructureListElement>) null;
 System.Collections.Generic.Dictionary<string, string> var_simpleStringMap = value.IsSetSimpleStringMap() ? value.SimpleStringMap : (System.Collections.Generic.Dictionary<string, string>) null;
 System.Collections.Generic.Dictionary<string, int> var_simpleIntegerMap = value.IsSetSimpleIntegerMap() ? value.SimpleIntegerMap : (System.Collections.Generic.Dictionary<string, int>) null;
 Simple.Aggregate.Deeply var_very = value.IsSetVery() ? value.Very : (Simple.Aggregate.Deeply) null;
 return new Dafny.Simple.Aggregate.Types.GetAggregateOutput ( ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M16_simpleStringList(var_simpleStringList) , ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M13_structureList(var_structureList) , ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M15_SimpleStringMap(var_simpleStringMap) , ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M16_SimpleIntegerMap(var_simpleIntegerMap) , ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M4_very(var_very) ) ;
}
 internal static Simple.Aggregate.SimpleAggregateConfig FromDafny_N6_simple__N9_aggregate__S21_SimpleAggregateConfig (Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig value) {
 Dafny.Simple.Aggregate.Types.SimpleAggregateConfig concrete = (Dafny.Simple.Aggregate.Types.SimpleAggregateConfig)value; Simple.Aggregate.SimpleAggregateConfig converted = new Simple.Aggregate.SimpleAggregateConfig();  return converted;
}
 internal static Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig ToDafny_N6_simple__N9_aggregate__S21_SimpleAggregateConfig (Simple.Aggregate.SimpleAggregateConfig value) {

 return new Dafny.Simple.Aggregate.Types.SimpleAggregateConfig (  ) ;
}
 internal static System.Collections.Generic.List<string> FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M16_simpleStringList (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N6_simple__N9_aggregate__S16_SimpleStringList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M16_simpleStringList (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N6_simple__N9_aggregate__S16_SimpleStringList((System.Collections.Generic.List<string>) value));
}
 internal static System.Collections.Generic.List<Simple.Aggregate.StructureListElement> FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M13_structureList (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> value) {
 return value.is_None ? (System.Collections.Generic.List<Simple.Aggregate.StructureListElement>) null : FromDafny_N6_simple__N9_aggregate__S13_StructureList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M13_structureList (System.Collections.Generic.List<Simple.Aggregate.StructureListElement> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>>.create_Some(ToDafny_N6_simple__N9_aggregate__S13_StructureList((System.Collections.Generic.List<Simple.Aggregate.StructureListElement>) value));
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M15_SimpleStringMap (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N6_simple__N9_aggregate__S15_SimpleStringMap(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M15_SimpleStringMap (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N6_simple__N9_aggregate__S15_SimpleStringMap((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static System.Collections.Generic.Dictionary<string, int> FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M16_SimpleIntegerMap (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, int>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, int>) null : FromDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, int>> ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M16_SimpleIntegerMap (System.Collections.Generic.Dictionary<string, int> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, int>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, int>>.create_Some(ToDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap((System.Collections.Generic.Dictionary<string, int>) value));
}
 internal static Simple.Aggregate.Deeply FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M4_very (Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> value) {
 return value.is_None ? (Simple.Aggregate.Deeply) null : FromDafny_N6_simple__N9_aggregate__S6_Deeply(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput__M4_very (Simple.Aggregate.Deeply value) {
 return value == null ? Wrappers_Compile.Option<Dafny.Simple.Aggregate.Types._IDeeply>.create_None() : Wrappers_Compile.Option<Dafny.Simple.Aggregate.Types._IDeeply>.create_Some(ToDafny_N6_simple__N9_aggregate__S6_Deeply((Simple.Aggregate.Deeply) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M16_simpleStringList (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.List<string>) null : FromDafny_N6_simple__N9_aggregate__S16_SimpleStringList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M16_simpleStringList (System.Collections.Generic.List<string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.create_Some(ToDafny_N6_simple__N9_aggregate__S16_SimpleStringList((System.Collections.Generic.List<string>) value));
}
 internal static System.Collections.Generic.List<Simple.Aggregate.StructureListElement> FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M13_structureList (Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> value) {
 return value.is_None ? (System.Collections.Generic.List<Simple.Aggregate.StructureListElement>) null : FromDafny_N6_simple__N9_aggregate__S13_StructureList(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M13_structureList (System.Collections.Generic.List<Simple.Aggregate.StructureListElement> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>>.create_Some(ToDafny_N6_simple__N9_aggregate__S13_StructureList((System.Collections.Generic.List<Simple.Aggregate.StructureListElement>) value));
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M15_SimpleStringMap (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, string>) null : FromDafny_N6_simple__N9_aggregate__S15_SimpleStringMap(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>> ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M15_SimpleStringMap (System.Collections.Generic.Dictionary<string, string> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>>>.create_Some(ToDafny_N6_simple__N9_aggregate__S15_SimpleStringMap((System.Collections.Generic.Dictionary<string, string>) value));
}
 internal static System.Collections.Generic.Dictionary<string, int> FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M16_SimpleIntegerMap (Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, int>> value) {
 return value.is_None ? (System.Collections.Generic.Dictionary<string, int>) null : FromDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>, int>> ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M16_SimpleIntegerMap (System.Collections.Generic.Dictionary<string, int> value) {
 return value == null ? Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, int>>.create_None() : Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>, int>>.create_Some(ToDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap((System.Collections.Generic.Dictionary<string, int>) value));
}
 internal static Simple.Aggregate.Deeply FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M4_very (Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> value) {
 return value.is_None ? (Simple.Aggregate.Deeply) null : FromDafny_N6_simple__N9_aggregate__S6_Deeply(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput__M4_very (Simple.Aggregate.Deeply value) {
 return value == null ? Wrappers_Compile.Option<Dafny.Simple.Aggregate.Types._IDeeply>.create_None() : Wrappers_Compile.Option<Dafny.Simple.Aggregate.Types._IDeeply>.create_Some(ToDafny_N6_simple__N9_aggregate__S6_Deeply((Simple.Aggregate.Deeply) value));
}
 internal static System.Collections.Generic.List<string> FromDafny_N6_simple__N9_aggregate__S16_SimpleStringList (Dafny.ISequence<Dafny.ISequence<char>> value) {
 return new System.Collections.Generic.List<string>(value.Elements.Select(FromDafny_N6_simple__N9_aggregate__S16_SimpleStringList__M6_member));
}
 internal static Dafny.ISequence<Dafny.ISequence<char>> ToDafny_N6_simple__N9_aggregate__S16_SimpleStringList (System.Collections.Generic.List<string> value) {
 return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(value.Select(ToDafny_N6_simple__N9_aggregate__S16_SimpleStringList__M6_member).ToArray());
}
 internal static System.Collections.Generic.List<Simple.Aggregate.StructureListElement> FromDafny_N6_simple__N9_aggregate__S13_StructureList (Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement> value) {
 return new System.Collections.Generic.List<Simple.Aggregate.StructureListElement>(value.Elements.Select(FromDafny_N6_simple__N9_aggregate__S13_StructureList__M6_member));
}
 internal static Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement> ToDafny_N6_simple__N9_aggregate__S13_StructureList (System.Collections.Generic.List<Simple.Aggregate.StructureListElement> value) {
 return Dafny.Sequence<Dafny.Simple.Aggregate.Types._IStructureListElement>.FromArray(value.Select(ToDafny_N6_simple__N9_aggregate__S13_StructureList__M6_member).ToArray());
}
 internal static System.Collections.Generic.Dictionary<string, string> FromDafny_N6_simple__N9_aggregate__S15_SimpleStringMap (Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>> value) {
 return value.ItemEnumerable.ToDictionary(pair => FromDafny_N6_simple__N9_aggregate__S15_SimpleStringMap__M3_key(pair.Car), pair => FromDafny_N6_simple__N9_aggregate__S15_SimpleStringMap__M5_value(pair.Cdr));
}
 internal static Dafny.IMap<Dafny.ISequence<char>, Dafny.ISequence<char>> ToDafny_N6_simple__N9_aggregate__S15_SimpleStringMap (System.Collections.Generic.Dictionary<string, string> value) {
 return Dafny.Map<Dafny.ISequence<char>, Dafny.ISequence<char>>.FromCollection(value.Select(pair =>
    new Dafny.Pair<Dafny.ISequence<char>, Dafny.ISequence<char>>(ToDafny_N6_simple__N9_aggregate__S15_SimpleStringMap__M3_key(pair.Key), ToDafny_N6_simple__N9_aggregate__S15_SimpleStringMap__M5_value(pair.Value))
));
}
 internal static System.Collections.Generic.Dictionary<string, int> FromDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap (Dafny.IMap<Dafny.ISequence<char>, int> value) {
 return value.ItemEnumerable.ToDictionary(pair => FromDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap__M3_key(pair.Car), pair => FromDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap__M5_value(pair.Cdr));
}
 internal static Dafny.IMap<Dafny.ISequence<char>, int> ToDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap (System.Collections.Generic.Dictionary<string, int> value) {
 return Dafny.Map<Dafny.ISequence<char>, int>.FromCollection(value.Select(pair =>
    new Dafny.Pair<Dafny.ISequence<char>, int>(ToDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap__M3_key(pair.Key), ToDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap__M5_value(pair.Value))
));
}
 internal static Simple.Aggregate.Deeply FromDafny_N6_simple__N9_aggregate__S6_Deeply (Dafny.Simple.Aggregate.Types._IDeeply value) {
 Dafny.Simple.Aggregate.Types.Deeply concrete = (Dafny.Simple.Aggregate.Types.Deeply)value; Simple.Aggregate.Deeply converted = new Simple.Aggregate.Deeply(); if (concrete._nested.is_Some) converted.Nested = (Simple.Aggregate.Nested) FromDafny_N6_simple__N9_aggregate__S6_Deeply__M6_nested(concrete._nested); return converted;
}
 internal static Dafny.Simple.Aggregate.Types._IDeeply ToDafny_N6_simple__N9_aggregate__S6_Deeply (Simple.Aggregate.Deeply value) {
 Simple.Aggregate.Nested var_nested = value.IsSetNested() ? value.Nested : (Simple.Aggregate.Nested) null;
 return new Dafny.Simple.Aggregate.Types.Deeply ( ToDafny_N6_simple__N9_aggregate__S6_Deeply__M6_nested(var_nested) ) ;
}
 internal static string FromDafny_N6_simple__N9_aggregate__S16_SimpleStringList__M6_member (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N6_simple__N9_aggregate__S16_SimpleStringList__M6_member (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Simple.Aggregate.StructureListElement FromDafny_N6_simple__N9_aggregate__S13_StructureList__M6_member (Dafny.Simple.Aggregate.Types._IStructureListElement value) {
 return FromDafny_N6_simple__N9_aggregate__S20_StructureListElement(value);
}
 internal static Dafny.Simple.Aggregate.Types._IStructureListElement ToDafny_N6_simple__N9_aggregate__S13_StructureList__M6_member (Simple.Aggregate.StructureListElement value) {
 return ToDafny_N6_simple__N9_aggregate__S20_StructureListElement(value);
}
 internal static string FromDafny_N6_simple__N9_aggregate__S15_SimpleStringMap__M3_key (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N6_simple__N9_aggregate__S15_SimpleStringMap__M3_key (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N6_simple__N9_aggregate__S15_SimpleStringMap__M5_value (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N6_simple__N9_aggregate__S15_SimpleStringMap__M5_value (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static string FromDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap__M3_key (Dafny.ISequence<char> value) {
 return FromDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static Dafny.ISequence<char> ToDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap__M3_key (string value) {
 return ToDafny_N6_smithy__N3_api__S6_String(value);
}
 internal static int FromDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap__M5_value (int value) {
 return FromDafny_N6_smithy__N3_api__S7_Integer(value);
}
 internal static int ToDafny_N6_simple__N9_aggregate__S16_SimpleIntegerMap__M5_value (int value) {
 return ToDafny_N6_smithy__N3_api__S7_Integer(value);
}
 internal static Simple.Aggregate.Nested FromDafny_N6_simple__N9_aggregate__S6_Deeply__M6_nested (Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._INested> value) {
 return value.is_None ? (Simple.Aggregate.Nested) null : FromDafny_N6_simple__N9_aggregate__S6_Nested(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._INested> ToDafny_N6_simple__N9_aggregate__S6_Deeply__M6_nested (Simple.Aggregate.Nested value) {
 return value == null ? Wrappers_Compile.Option<Dafny.Simple.Aggregate.Types._INested>.create_None() : Wrappers_Compile.Option<Dafny.Simple.Aggregate.Types._INested>.create_Some(ToDafny_N6_simple__N9_aggregate__S6_Nested((Simple.Aggregate.Nested) value));
}
 internal static string FromDafny_N6_smithy__N3_api__S6_String (Dafny.ISequence<char> value) {
 return new string(value.Elements);
}
 internal static Dafny.ISequence<char> ToDafny_N6_smithy__N3_api__S6_String (string value) {
 return Dafny.Sequence<char>.FromString(value);
}
 internal static Simple.Aggregate.StructureListElement FromDafny_N6_simple__N9_aggregate__S20_StructureListElement (Dafny.Simple.Aggregate.Types._IStructureListElement value) {
 Dafny.Simple.Aggregate.Types.StructureListElement concrete = (Dafny.Simple.Aggregate.Types.StructureListElement)value; Simple.Aggregate.StructureListElement converted = new Simple.Aggregate.StructureListElement(); if (concrete._s.is_Some) converted.S = (string) FromDafny_N6_simple__N9_aggregate__S20_StructureListElement__M1_s(concrete._s);
 if (concrete._i.is_Some) converted.I = (int) FromDafny_N6_simple__N9_aggregate__S20_StructureListElement__M1_i(concrete._i); return converted;
}
 internal static Dafny.Simple.Aggregate.Types._IStructureListElement ToDafny_N6_simple__N9_aggregate__S20_StructureListElement (Simple.Aggregate.StructureListElement value) {
 string var_s = value.IsSetS() ? value.S : (string) null;
 int? var_i = value.IsSetI() ? value.I : (int?) null;
 return new Dafny.Simple.Aggregate.Types.StructureListElement ( ToDafny_N6_simple__N9_aggregate__S20_StructureListElement__M1_s(var_s) , ToDafny_N6_simple__N9_aggregate__S20_StructureListElement__M1_i(var_i) ) ;
}
 internal static int FromDafny_N6_smithy__N3_api__S7_Integer (int value) {
 return value;
}
 internal static int ToDafny_N6_smithy__N3_api__S7_Integer (int value) {
 return value;
}
 internal static Simple.Aggregate.Nested FromDafny_N6_simple__N9_aggregate__S6_Nested (Dafny.Simple.Aggregate.Types._INested value) {
 Dafny.Simple.Aggregate.Types.Nested concrete = (Dafny.Simple.Aggregate.Types.Nested)value; Simple.Aggregate.Nested converted = new Simple.Aggregate.Nested(); if (concrete._value.is_Some) converted.Value = (string) FromDafny_N6_simple__N9_aggregate__S6_Nested__M5_value(concrete._value); return converted;
}
 internal static Dafny.Simple.Aggregate.Types._INested ToDafny_N6_simple__N9_aggregate__S6_Nested (Simple.Aggregate.Nested value) {
 string var_value = value.IsSetValue() ? value.Value : (string) null;
 return new Dafny.Simple.Aggregate.Types.Nested ( ToDafny_N6_simple__N9_aggregate__S6_Nested__M5_value(var_value) ) ;
}
 internal static string FromDafny_N6_simple__N9_aggregate__S20_StructureListElement__M1_s (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N6_simple__N9_aggregate__S20_StructureListElement__M1_s (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string) value));
}
 internal static int? FromDafny_N6_simple__N9_aggregate__S20_StructureListElement__M1_i (Wrappers_Compile._IOption<int> value) {
 return value.is_None ? (int?) null : FromDafny_N6_smithy__N3_api__S7_Integer(value.Extract());
}
 internal static Wrappers_Compile._IOption<int> ToDafny_N6_simple__N9_aggregate__S20_StructureListElement__M1_i (int? value) {
 return value == null ? Wrappers_Compile.Option<int>.create_None() : Wrappers_Compile.Option<int>.create_Some(ToDafny_N6_smithy__N3_api__S7_Integer((int) value));
}
 internal static string FromDafny_N6_simple__N9_aggregate__S6_Nested__M5_value (Wrappers_Compile._IOption<Dafny.ISequence<char>> value) {
 return value.is_None ? (string) null : FromDafny_N6_smithy__N3_api__S6_String(value.Extract());
}
 internal static Wrappers_Compile._IOption<Dafny.ISequence<char>> ToDafny_N6_simple__N9_aggregate__S6_Nested__M5_value (string value) {
 return value == null ? Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None() : Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(ToDafny_N6_smithy__N3_api__S6_String((string) value));
}
 public static System.Exception FromDafny_CommonError(Dafny.Simple.Aggregate.Types._IError value) {
 switch(value)
 {

 case Dafny.Simple.Aggregate.Types.Error_Opaque dafnyVal:
 return new OpaqueError(dafnyVal._obj);
 default:
 // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
 return new OpaqueError();
}
}
 public static Dafny.Simple.Aggregate.Types._IError ToDafny_CommonError(System.Exception value) {
 switch (value)
 {

 // OpaqueError is redundant, but listed for completeness.
 case OpaqueError exception:
 return new Dafny.Simple.Aggregate.Types.Error_Opaque(exception);
 case System.Exception exception:
 return new Dafny.Simple.Aggregate.Types.Error_Opaque(exception);
 default:
 // The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)
 return new Dafny.Simple.Aggregate.Types.Error_Opaque(value);
}
}
}
}
