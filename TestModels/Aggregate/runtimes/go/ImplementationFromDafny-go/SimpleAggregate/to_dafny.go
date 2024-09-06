// Code generated by smithy-go-codegen DO NOT EDIT.

package SimpleAggregate

import (
	"github.com/dafny-lang/DafnyRuntimeGo/dafny"
	"github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	"github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/SimpleAggregateTypes"
)

func GetAggregateInput_ToDafny(nativeInput SimpleAggregateTypes.GetAggregateInput_smithygenerated) SimpleAggregateTypes.GetAggregateInput {

	return func() SimpleAggregateTypes.GetAggregateInput{

		return SimpleAggregateTypes.Companion_GetAggregateInput_.Create_GetAggregateInput_(func() Wrappers.Option {
			if nativeInput.SimpleStringList == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			var fieldValue []interface{} = make([]interface{}, 0)
			for _, val := range nativeInput.SimpleStringList {
				element := func() dafny.Sequence {

					return dafny.SeqOfChars([]dafny.Char(val)...)
				}()
				fieldValue = append(fieldValue, element)
			}
			return Wrappers.Companion_Option_.Create_Some_(dafny.SeqOf(fieldValue...))
		}(), func() Wrappers.Option {
			if nativeInput.StructureList == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			var fieldValue []interface{} = make([]interface{}, 0)
			for _, val := range nativeInput.StructureList {
				element := func() SimpleAggregateTypes.StructureListElement {

					return SimpleAggregateTypes.Companion_StructureListElement_.Create_StructureListElement_(func() Wrappers.Option {
						if val.StringValue == nil {
							return Wrappers.Companion_Option_.Create_None_()
						}
						return Wrappers.Companion_Option_.Create_Some_(dafny.SeqOfChars([]dafny.Char(*val.StringValue)...))
					}(), func() Wrappers.Option {
						if val.IntegerValue == nil {
							return Wrappers.Companion_Option_.Create_None_()
						}
						return Wrappers.Companion_Option_.Create_Some_(*val.IntegerValue)
					}())
				}()
				fieldValue = append(fieldValue, element)
			}
			return Wrappers.Companion_Option_.Create_Some_(dafny.SeqOf(fieldValue...))
		}(), func() Wrappers.Option {
			if nativeInput.SimpleStringMap == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			fieldValue := dafny.NewMapBuilder()
			for key, val := range nativeInput.SimpleStringMap {
				fieldValue.Add(func() dafny.Sequence {

					return dafny.SeqOfChars([]dafny.Char(key)...)
				}(), func() dafny.Sequence {

					return dafny.SeqOfChars([]dafny.Char(val)...)
				}())
			}
			return Wrappers.Companion_Option_.Create_Some_(fieldValue.ToMap())
		}(), func() Wrappers.Option {
			if nativeInput.SimpleIntegerMap == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			fieldValue := dafny.NewMapBuilder()
			for key, val := range nativeInput.SimpleIntegerMap {
				fieldValue.Add(func() dafny.Sequence {

					return dafny.SeqOfChars([]dafny.Char(key)...)
				}(), func() interface{} {

					return val
				}())
			}
			return Wrappers.Companion_Option_.Create_Some_(fieldValue.ToMap())
		}(), func() Wrappers.Option {
			if nativeInput.NestedStructure == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			return Wrappers.Companion_Option_.Create_Some_(SimpleAggregateTypes.Companion_NestedStructure_.Create_NestedStructure_(func() Wrappers.Option {
				if nativeInput.NestedStructure.StringStructure == nil {
					return Wrappers.Companion_Option_.Create_None_()
				}
				return Wrappers.Companion_Option_.Create_Some_(SimpleAggregateTypes.Companion_StringStructure_.Create_StringStructure_(func() Wrappers.Option {
					if nativeInput.NestedStructure.StringStructure.Value == nil {
						return Wrappers.Companion_Option_.Create_None_()
					}
					return Wrappers.Companion_Option_.Create_Some_(dafny.SeqOfChars([]dafny.Char(*nativeInput.NestedStructure.StringStructure.Value)...))
				}()))
			}()))
		}())
	}()

}

func GetAggregateOutput_ToDafny(nativeOutput SimpleAggregateTypes.GetAggregateOutput_smithygenerated) SimpleAggregateTypes.GetAggregateOutput {

	return func() SimpleAggregateTypes.GetAggregateOutput {

		return SimpleAggregateTypes.Companion_GetAggregateOutput_.Create_GetAggregateOutput_(func() Wrappers.Option {
			if nativeOutput.SimpleStringList == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			var fieldValue []interface{} = make([]interface{}, 0)
			for _, val := range nativeOutput.SimpleStringList {
				element := func() dafny.Sequence {

					return dafny.SeqOfChars([]dafny.Char(val)...)
				}()
				fieldValue = append(fieldValue, element)
			}
			return Wrappers.Companion_Option_.Create_Some_(dafny.SeqOf(fieldValue...))
		}(), func() Wrappers.Option {
			if nativeOutput.StructureList == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			var fieldValue []interface{} = make([]interface{}, 0)
			for _, val := range nativeOutput.StructureList {
				element := func() SimpleAggregateTypes.StructureListElement {

					return SimpleAggregateTypes.Companion_StructureListElement_.Create_StructureListElement_(func() Wrappers.Option {
						if val.StringValue == nil {
							return Wrappers.Companion_Option_.Create_None_()
						}
						return Wrappers.Companion_Option_.Create_Some_(dafny.SeqOfChars([]dafny.Char(*val.StringValue)...))
					}(), func() Wrappers.Option {
						if val.IntegerValue == nil {
							return Wrappers.Companion_Option_.Create_None_()
						}
						return Wrappers.Companion_Option_.Create_Some_(*val.IntegerValue)
					}())
				}()
				fieldValue = append(fieldValue, element)
			}
			return Wrappers.Companion_Option_.Create_Some_(dafny.SeqOf(fieldValue...))
		}(), func() Wrappers.Option {
			if nativeOutput.SimpleStringMap == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			fieldValue := dafny.NewMapBuilder()
			for key, val := range nativeOutput.SimpleStringMap {
				fieldValue.Add(func() dafny.Sequence {

					return dafny.SeqOfChars([]dafny.Char(key)...)
				}(), func() dafny.Sequence {

					return dafny.SeqOfChars([]dafny.Char(val)...)
				}())
			}
			return Wrappers.Companion_Option_.Create_Some_(fieldValue.ToMap())
		}(), func() Wrappers.Option {
			if nativeOutput.SimpleIntegerMap == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			fieldValue := dafny.NewMapBuilder()
			for key, val := range nativeOutput.SimpleIntegerMap {
				fieldValue.Add(func() dafny.Sequence {

					return dafny.SeqOfChars([]dafny.Char(key)...)
				}(), func() interface{} {

					return val
				}())
			}
			return Wrappers.Companion_Option_.Create_Some_(fieldValue.ToMap())
		}(), func() Wrappers.Option {
			if nativeOutput.NestedStructure == nil {
				return Wrappers.Companion_Option_.Create_None_()
			}
			return Wrappers.Companion_Option_.Create_Some_(SimpleAggregateTypes.Companion_NestedStructure_.Create_NestedStructure_(func() Wrappers.Option {
				if nativeOutput.NestedStructure.StringStructure == nil {
					return Wrappers.Companion_Option_.Create_None_()
				}
				return Wrappers.Companion_Option_.Create_Some_(SimpleAggregateTypes.Companion_StringStructure_.Create_StringStructure_(func() Wrappers.Option {
					if nativeOutput.NestedStructure.StringStructure.Value == nil {
						return Wrappers.Companion_Option_.Create_None_()
					}
					return Wrappers.Companion_Option_.Create_Some_(dafny.SeqOfChars([]dafny.Char(*nativeOutput.NestedStructure.StringStructure.Value)...))
				}()))
			}()))
		}())
	}()

}

func CollectionOfErrors_Input_ToDafny(nativeInput SimpleAggregateTypes.CollectionOfErrors) SimpleAggregateTypes.Error {
	var e []interface{}
	for _, i2 := range nativeInput.ListOfErrors {
		e = append(e, Error_ToDafny(i2))
	}
	return SimpleAggregateTypes.Companion_Error_.Create_CollectionOfErrors_(dafny.SeqOf(e...), dafny.SeqOfChars([]dafny.Char(nativeInput.Message)...))
}
// func OpaqueError_Input_ToDafny(nativeInput SimpleAggregateTypes.OpaqueError) SimpleAggregateTypes.Error {
// 	return SimpleAggregateTypes.Companion_Error_.Create_Opaque_(nativeInput.ErrObject)
// }

func Error_ToDafny(err error) SimpleAggregateTypes.Error {
	switch err.(type) {
	// Service Errors

	//DependentErrors

	//Unmodelled Errors
	case SimpleAggregateTypes.CollectionOfErrors:
		return CollectionOfErrors_Input_ToDafny(err.(SimpleAggregateTypes.CollectionOfErrors))

	default:
	// 	error, ok := err.(SimpleAggregateTypes.OpaqueError)
	// 	if !ok {
	// 		panic("Error is not an OpaqueError")
	// 	}
		// return OpaqueError_Input_ToDafny("error")
		return CollectionOfErrors_Input_ToDafny(err.(SimpleAggregateTypes.CollectionOfErrors))
	}
}

func SimpleAggregateConfig_ToDafny(nativeInput SimpleAggregateTypes.SimpleAggregateConfig_smithygenerated) SimpleAggregateTypes.SimpleAggregateConfig {
	return func() SimpleAggregateTypes.SimpleAggregateConfig {

		return SimpleAggregateTypes.Companion_SimpleAggregateConfig_.Create_SimpleAggregateConfig_()
	}()

}
