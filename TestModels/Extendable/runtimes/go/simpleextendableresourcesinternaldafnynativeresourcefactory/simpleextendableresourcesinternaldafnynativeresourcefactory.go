// Package simpleextendableresourcesinternaldafnynativeresourcefactory
// Dafny module simpleextendableresourcesinternaldafnynativeresourcefactory compiled into Go

package simpleextendableresourcesinternaldafnynativeresourcefactory

import (
	os "os"

	ExtendableResource "github.com/Smithy-dafny/TestModels/Extern/ExtendableResource"
	SimpleExtendableResourcesOperations "github.com/Smithy-dafny/TestModels/Extern/SimpleExtendableResourcesOperations"
	simpleextendableresources "github.com/Smithy-dafny/TestModels/Extern/simpleextendableresources"
	simpleextendableresourcesinternaldafnytypes "github.com/Smithy-dafny/TestModels/Extern/simpleextendableresourcesinternaldafnytypes"
	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	StandardLibrary "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	StandardLibraryInterop "github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ StandardLibraryInterop.Dummy__
var _ ExtendableResource.Dummy__
var _ SimpleExtendableResourcesOperations.Dummy__

type Dummy__ struct{}

func DafnyFactory() simpleextendableresourcesinternaldafnytypes.IExtendableResource {
	extendableResource := ExtendableResource.New_ExtendableResource_()
	extendableResource.OfName(_dafny.SeqOfString("dafny-default"))
	return &simpleextendableresources.NativeWrapper{Impl: simpleextendableresources.ToNativeExtendableResource(extendableResource)}
}
