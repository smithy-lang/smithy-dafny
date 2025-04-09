package ExternDefinitions

import (
	Wrappers "github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library/Wrappers"
	OrphanedResource "github.com/smithy-lang/smithy-dafny/TestModels/OrphanedShapes/OrphanedResource"
	SimpleOrphanedTypes "github.com/smithy-lang/smithy-dafny/TestModels/OrphanedShapes/SimpleOrphanedTypes"
	simpleorphanedsmithygenerated "github.com/smithy-lang/smithy-dafny/TestModels/OrphanedShapes/simpleorphanedsmithygenerated"
	simpleorphanedsmithygeneratedtypes "github.com/smithy-lang/smithy-dafny/TestModels/OrphanedShapes/simpleorphanedsmithygeneratedtypes"
)

var _ Wrappers.Dummy__

// TODO: Remove this once Dafny bug is fixed.
// Dafny bug: https://t.corp.amazon.com/9a9028fd-2711-4843-b8f0-09965f7e61a7/communication#f03694be-7410-47f9-866d-e43093b018f9
var m_ExternDefinitions = CompanionStruct_Default___{}

func (CompanionStruct_Default___) InitializeOrphanedStructure(input SimpleOrphanedTypes.OrphanedStructure) SimpleOrphanedTypes.OrphanedStructure {
	nativeInput := simpleorphanedsmithygenerated.OrphanedStructure_FromDafny(input)
	stringToReplace := "the extern MUST use Smithy-generated conversions to set this value in the native structure"
	nativeInput.StringValue = &stringToReplace
	dafnyInitializedStructure := simpleorphanedsmithygenerated.OrphanedStructure_ToDafny(nativeInput)
	return dafnyInitializedStructure
}

func (CompanionStruct_Default___) CallNativeOrphanedResource(input *OrphanedResource.OrphanedResource) Wrappers.Result {
	native_resource := simpleorphanedsmithygenerated.OrphanedResource_FromDafny(input)
	someString := "the extern MUST provide this string to the native resource's operation"
	native_output, err := native_resource.OrphanedResourceOperation(simpleorphanedsmithygeneratedtypes.OrphanedResourceOperationInput{SomeString: &someString})
	if err != nil {
		return Wrappers.Companion_Result_.Create_Failure_(err)
	}
	dafny_output := simpleorphanedsmithygenerated.OrphanedResourceOperationOutput_ToDafny(*native_output)
	return Wrappers.Companion_Result_.Create_Success_(dafny_output)
}

func (CompanionStruct_Default___) CallNativeOrphanedError(input SimpleOrphanedTypes.Error) SimpleOrphanedTypes.Error {
	native_error := simpleorphanedsmithygenerated.Error_FromDafny(input).(simpleorphanedsmithygeneratedtypes.OrphanedError)
	native_error.Message = "the extern MUST set this string using the catch-all error converter, NOT the orphaned error-specific converter"
	dafny_error_again := simpleorphanedsmithygenerated.Error_ToDafny(native_error)
	return dafny_error_again
}
