package NativeResourceFactory

import (
	"github.com/dafny-lang/DafnyRuntimeGo/v4/dafny"
	ExtendableResource "github.com/smithy-lang/smithy-dafny/TestModels/Extendable/ExtendableResource"
	SimpleExtendableResourcesTypes "github.com/smithy-lang/smithy-dafny/TestModels/Extendable/SimpleExtendableResourcesTypes"
	"github.com/smithy-lang/smithy-dafny/TestModels/Extendable/test/simpleextendableresourcessmithygenerated"
)

func DafnyFactory() SimpleExtendableResourcesTypes.IExtendableResource {
	extendableResource := ExtendableResource.New_ExtendableResource_()
	extendableResource.OfName(dafny.SeqOfString("dafny-default"))
	return &simpleextendableresourcessmithygenerated.ExtendableResourceNativeWrapper{Impl: simpleextendableresourcessmithygenerated.ExtendableResource_FromDafny(extendableResource)}
}
